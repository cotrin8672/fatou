// Exercise the Fatou stdio server with real Windows SMB workspaces.
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';

const [binary, uncRoot, driveRoot, fixtureHome] = process.argv.slice(2);
assert.ok(binary && uncRoot && driveRoot && fixtureHome, 'usage: node windows-network-smoke.mjs FATOU UNC DRIVE USERPROFILE');
const encode = (path) => path.split('/').map(encodeURIComponent).join('/');
const unc = uncRoot.replaceAll('\\', '/').replace(/^\/\//, '');
const drive = driveRoot.replaceAll('\\', '/');
const [host, ...share] = unc.split('/');
assert.ok(host && share.length, `invalid UNC path: ${uncRoot}`);
assert.match(drive, /^[A-Za-z]:\//);
const folderKind = 19;
const fileKind = 17;
const childEnv = { ...process.env };
for (const key of Object.keys(childEnv)) {
  if (/^(HOME|USERPROFILE|JULIA_DEPOT_PATH|JULIA_PROJECT)$/i.test(key)) delete childEnv[key];
}
childEnv.HOME = fixtureHome + '-wrong-home';
childEnv.USERPROFILE = fixtureHome;

class Lsp {
  id = 0;
  pending = new Map();
  buffer = Buffer.alloc(0);
  stderr = '';
  failure = null;

  constructor() {
    this.process = spawn(binary, ['--no-config', 'lsp'], { windowsHide: true, env: childEnv });
    this.process.stderr.on('data', (chunk) => { this.stderr += chunk; });
    this.process.stdout.on('data', (chunk) => {
      try {
        this.buffer = Buffer.concat([this.buffer, chunk]);
        this.receive();
      } catch (err) {
        this.fail(err);
        this.process.kill();
      }
    });
    this.process.once('error', (err) => this.fail(err));
    this.process.once('exit', (code, signal) => this.fail(new Error(`Fatou exited: ${code ?? signal}\n${this.stderr}`)));
    this.process.stdin.on('error', (err) => this.fail(err));
  }

  send(message) {
    const body = Buffer.from(JSON.stringify({ jsonrpc: '2.0', ...message }));
    this.process.stdin.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`), body]));
  }

  receive() {
    for (;;) {
      const end = this.buffer.indexOf('\r\n\r\n');
      if (end === -1) return;
      const head = this.buffer.subarray(0, end).toString('ascii');
      const match = /(?:^|\r\n)Content-Length: (\d+)/i.exec(head);
      assert.ok(match, `missing Content-Length: ${head}`);
      const start = end + 4;
      const next = start + Number(match[1]);
      if (this.buffer.length < next) return;
      const msg = JSON.parse(this.buffer.subarray(start, next));
      this.buffer = this.buffer.subarray(next);
      if (msg.method !== undefined) {
        if (msg.id !== undefined) {
          const result = msg.method === 'workspace/configuration' ? (msg.params.items ?? []).map(() => null) : null;
          this.send({ id: msg.id, result });
        }
      } else {
        const callback = this.pending.get(msg.id);
        if (callback) {
          this.pending.delete(msg.id);
          callback(msg);
        }
      }
    }
  }

  fail(err) {
    this.failure = err;
    for (const callback of this.pending.values()) callback({ error: err });
    this.pending.clear();
  }

  request(method, params) {
    if (this.failure) return Promise.reject(this.failure);
    const id = ++this.id;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`timed out waiting for ${method}\n${this.stderr}`));
      }, 30_000);
      this.pending.set(id, (message) => {
        clearTimeout(timer);
        if ('error' in message) reject(new Error(`${method}: ${message.error.message ?? JSON.stringify(message.error)}`));
        else resolve(message.result);
      });
      this.send({ id, method, params });
    });
  }
}

async function check(rootUri, title, uri = `${rootUri}/entry.jl`) {
  const lsp = new Lsp();
  try {
    await lsp.request('initialize', {
      processId: process.pid,
      rootUri,
      workspaceFolders: [{ uri: rootUri, name: 'SMB fixture' }],
      capabilities: { general: { positionEncodings: ['utf-16'] } },
    });
    lsp.send({ method: 'initialized', params: {} });
    let version = 0;
    const complete = async (marked, ready = (items) => items.some(({ kind }) => kind === folderKind || kind === fileKind), context) => {
      const [before, after] = marked.split('¦');
      assert.notEqual(after, undefined);
      const text = before + after;
      version++;
      if (version === 1) {
        lsp.send({ method: 'textDocument/didOpen', params: { textDocument: { uri, languageId: 'julia', version, text } } });
      } else {
        lsp.send({
          method: 'textDocument/didChange',
          params: { textDocument: { uri, version }, contentChanges: [{ text }] },
        });
      }
      const lines = before.split('\n');
      const position = { line: lines.length - 1, character: lines.at(-1).length };
      // The package index can be asynchronous. Poll for the specific expected
      // class or member, never just for a non-empty response.
      let items;
      for (let i = 0; i < 30; i++) {
        const result = await lsp.request('textDocument/completion', { textDocument: { uri }, position, context });
        items = Array.isArray(result) ? result : (result?.items ?? []);
        if (ready(items)) return items;
        await new Promise((resolve) => setTimeout(resolve, 250));
      }
      return items;
    };
    let items = await complete('src = joinpath(@__DIR__, "result¦t_stdout")');
    const folder = items.find(({ label, kind }) => label === 'result_stdout' && kind === folderKind);
    assert.ok(folder, `${title}: missing joinpath folder; got ${items.slice(0, 15).map(({ label }) => label)}`);
    assert.equal(folder.textEdit.newText, 'result_stdout/');
    const exact = 'src = joinpath(@__DIR__, "resultt_stdout")';
    const { range } = folder.textEdit;
    assert.equal(exact.slice(range.start.character, range.end.character), 'resultt_stdout');
    assert.ok(items.some(({ label, kind }) => label === 'result_data.toml' && kind === fileKind), `${title}: missing joinpath non-Julia file`);
    assert.ok(items.every(({ kind }) => kind === folderKind || kind === fileKind), `${title}: non-path item leaked into joinpath`);

    items = await complete('include("result¦")');
    assert.ok(items.some(({ label, kind }) => label === 'result_stdout' && kind === folderKind), `${title}: missing include folder`);
    assert.ok(items.some(({ label, kind }) => label === 'result_script.jl' && kind === fileKind), `${title}: missing include source`);
    assert.ok(!items.some(({ label }) => label === 'result_data.toml'), `${title}: non-Julia file leaked into include`);

    items = await complete('src = joinpath(@__DIR__, "result_stdout/ch¦")');
    assert.ok(items.some(({ label, kind }) => label === 'child.txt' && kind === fileKind), `${title}: missing nested file`);

    // The fixture uses normal manifest UUID/tree/slug resolution on Windows,
    // with no explicit depot override and a deliberately wrong HOME.
    for (const [source, label] of [
      ['import MAT\nd = MAT.mat¦', 'matread'],
      ['d = MAT.mat¦', 'matread'],
      ['using Roots: fi¦', 'find_zero'],
    ]) {
      const matching = (candidates) => candidates.some((candidate) => candidate.label === label);
      items = await complete(source, matching);
      assert.ok(matching(items), `${title}: missing ${label} in ${source}; got ${items.slice(0, 15).map(({ label }) => label)}`);
    }
    const same = (label) => (candidates) => candidates.some((item) => item.label === label);
    const taskSource = 'using Random\nfunction run()\n    tasks = [\n        ';
    items = await complete(taskSource + 'Dag¦\n    ]\nend', same('Dagger'));
    const dagger = items.find((item) => item.label === 'Dagger');
    assert.match(dagger?.additionalTextEdits?.[0]?.newText ?? '', /^import Dagger\r?\n$/);
    for (const [name, prefix, context, mustImport] of [
      ['unimported', '', { triggerKind: 2, triggerCharacter: '@' }, true],
      ['unimported retry', '', { triggerKind: 3 }, true],
      ['imported', 'using Dagger\n', { triggerKind: 1 }, false],
    ]) {
      items = await complete(prefix + taskSource + 'Dagger.@s¦\n    ]\nend', same('@spawn'), context);
      const spawn = items.find((item) => item.label === '@spawn');
      assert.equal(spawn?.textEdit?.newText, 'spawn', `${title}: ${name} macro must preserve @`);
      assert.equal(!!spawn.additionalTextEdits?.some((edit) => /^import Dagger\r?\n$/.test(edit.newText)), mustImport);
    }
    items = await complete('using FFTW\nfunction run(xs)\n    map(xs) do x\n        abs2.(ff¦(x))\n    end\nend', same('fft'));
    assert.ok(same('fft')(items), `${title}: FFTW re-export is missing`);
    await lsp.request('shutdown', null);
    lsp.send({ method: 'exit' });
    console.log(`PASS: ${title} ${rootUri}`);
  } finally {
    lsp.process.kill();
  }
}

await check(`file://${host}/${encode(share.join('/'))}/source%20folder`, 'UNC authority');
await check(`file:////${host}/${encode(share.join('/'))}/source%20folder`, 'UNC path');
// vim.uri_from_fname in Neovim 0.11 does not normalize a backslash UNC filename
// as it does a drive path; the UNC is percent-encoded after file://.
const nvimUnc = `file://${encodeURIComponent(uncRoot)}%5Csource%20folder`;
await check(nvimUnc, 'UNC Neovim 0.11', `${nvimUnc}%5Centry.jl`);
await check(`file:///${drive.slice(0, 3)}${encode(drive.slice(3))}`.replace(/\/$/, '') + '/source%20folder', 'SMB mapped drive');
