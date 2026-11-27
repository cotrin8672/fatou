// Exercise the binary through stdio and real, pinned Julia package sources.
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { resolve, join, delimiter } from 'node:path';
import { pathToFileURL } from 'node:url';
import { setTimeout as pause } from 'node:timers/promises';

const juliaLoadPath = ['@', '@stdlib'].join(delimiter);
const [binary, project] = process.argv.slice(2).map(x => resolve(x));
assert(binary && project && existsSync(join(project, 'Project.toml')));
const root = pathToFileURL(project).href;
const child = spawn(binary, ['--no-config', 'lsp'], {
  cwd: project,
  env: { ...process.env, JULIA_LOAD_PATH: juliaLoadPath },
  stdio: ['pipe', 'pipe', 'inherit'],
});
let nextId = 1;
const pending = new Map();
let queued = Buffer.alloc(0);
function send(msg) {
  const data = Buffer.from(JSON.stringify({ jsonrpc: '2.0', ...msg }), 'utf8');
  child.stdin.write(`Content-Length: ${data.length}\r\n\r\n`);
  child.stdin.write(data);
}
child.on('error', err => {
  for (const p of pending.values()) p.reject(err);
  pending.clear();
});
child.on('exit', code => {
  for (const p of pending.values()) p.reject(new Error(`Fatou exited (${code})`));
  pending.clear();
});
child.stdout.on('data', part => {
  queued = Buffer.concat([queued, part]);
  for (;;) {
    const end = queued.indexOf('\r\n\r\n');
    if (end < 0) return;
    const length = Number(/Content-Length:\s*(\d+)/i.exec(queued.subarray(0, end).toString())?.[1]);
    assert(Number.isInteger(length), 'Invalid JSON-RPC frame');
    if (queued.length < end + 4 + length) return;
    const body = JSON.parse(queued.subarray(end + 4, end + 4 + length));
    queued = queued.subarray(end + 4 + length);
    if (body.method && body.id !== undefined) {
      const items = body.params?.items || [];
      send({ id: body.id, result: body.method === 'workspace/configuration' ? items.map(() => null) : null });
    } else if (pending.has(body.id)) {
      const p = pending.get(body.id);
      pending.delete(body.id);
      body.error ? p.reject(Object.assign(new Error(body.error.message), body.error)) : p.resolve(body.result);
    }
  }
});
function request(method, params, timeout = 25_000) {
  const id = nextId++;
  return new Promise((res, rej) => {
    const timer = setTimeout(() => {
      pending.delete(id);
      rej(new Error(`Timed out on ${method}`));
    }, timeout);
    pending.set(id, {
      resolve: value => { clearTimeout(timer); res(value); },
      reject: error => { clearTimeout(timer); rej(error); },
    });
    send({ id, method, params });
  });
}
function snippet(name, marked) {
  const [before, after] = marked.split('│');
  assert.notEqual(after, undefined);
  const lines = before.split('\n');
  const position = { line: lines.length - 1, character: lines.at(-1).length };
  const text = before + after;
  const uri = pathToFileURL(join(project, `smoke_${name}.jl`)).href;
  send({ method: 'textDocument/didOpen', params: { textDocument: {
    uri, languageId: 'julia', version: 1, text,
  }}});
  return {
    uri, text, position,
    params: { textDocument: { uri }, position, context: { triggerKind: 1 } },
    close: () => send({ method: 'textDocument/didClose', params: { textDocument: { uri } } }),
  };
}
const asItems = result => Array.isArray(result) ? result : result?.items || [];
async function has(name, code, label, { retry = false, check } = {}) {
  const doc = snippet(name, code);
  try {
    const deadline = Date.now() + (retry ? 175_000 : 25_000);
    for (;;) {
      let result;
      try {
        result = await request('textDocument/completion', doc.params);
      } catch (error) {
        if (error.code !== -32801 || Date.now() >= deadline) throw error;
        await pause(250);
        continue;
      }
      const item = asItems(result).find(x => x.label === label);
      if (item) {
        if (check) await check(item, result, doc);
        console.log(`${name}: ${label}`);
        return;
      }
      if (!retry || Date.now() >= deadline) {
        assert.fail(`${name} missing ${label}; got ${asItems(result).slice(0, 20).map(x => x.label)}`);
      }
      await pause(350);
    }
  } finally {
    doc.close();
  }
}
const autoImportPrograms = [];
async function importEdit(item, doc, prefix, pattern) {
  if (!item.additionalTextEdits?.length && item.data) {
    item = await request('completionItem/resolve', item);
  }
  assert(item.additionalTextEdits?.some(edit => pattern.test(edit.newText)), JSON.stringify(item));
  const edit = item.textEdit
    ? { range: item.textEdit.range || item.textEdit.replace, newText: item.textEdit.newText }
    : { range: { start: { ...doc.position, character: doc.position.character - prefix.length }, end: doc.position },
        newText: item.insertText || item.label };
  const lines = doc.text.split('\n');
  function offset(pos) {
    return lines.slice(0, pos.line).reduce((sum, line) => sum + line.length + 1, 0) + pos.character;
  }
  const edits = [edit, ...item.additionalTextEdits].map(e => ({
    start: offset(e.range.start), end: offset(e.range.end), newText: e.newText,
  })).sort((a,b) => b.start - a.start || b.end - a.end);
  let previous = doc.text.length;
  let result = doc.text;
  for (const e of edits) {
    assert(e.start <= e.end && e.end <= previous, 'Overlapping or invalid completion edits');
    result = result.slice(0, e.start) + e.newText + result.slice(e.end);
    previous = e.start;
  }
  assert(result.startsWith('module Audit'), 'Import must stay in the consuming module');
  autoImportPrograms.push(result.replace(/^module Audit/, `module Audit${autoImportPrograms.length + 1}`));
}

try {
  await request('initialize', {rootUri: root, processId: process.pid,
    workspaceFolders: [{uri: root, name: 'editor-regressions'}],
    capabilities: {general: {positionEncodings: ['utf-16']}},
  });
  send({method: 'initialized', params: {}});
  await has('dagger_first_character', 'function run()\n tasks = [\n D│\n ]\nend', 'Dagger', {
    retry: true, check: (item) => assert.match(item.additionalTextEdits?.[0]?.newText ?? '', /^import Dagger\r?\n$/),
  });
  await has('dagger_module', 'module Audit\nrun() = [\n Dag│\n]\n@assert only(run()) === Dagger\nend', 'Dagger', {
    retry: true, check: (item, _result, doc) => importEdit(item, doc, 'Dag', /^import Dagger\r?\n$/),
  });
  await has('dagger_index_ready', 'using Dagger: @sp│\n', '@spawn', {retry: true});
  await has('dagger_macro', 'module Audit\nrun() = [\n Dagger.@s│ begin\n 21 + 21\n end\n]\n@assert fetch(only(run())) == 42\nend', '@spawn', {
    check: async (item, _result, doc) => {
      assert.equal(item.filterText, 'spawn');
      assert.equal(item.textEdit.newText, 'spawn');
      await importEdit(item, doc, 's', /^import Dagger\r?\n$/);
    },
  });
  await has('dagger_macro_imported', 'using Dagger\nrun() = [\n Dagger.@s│ begin 42 end\n]\n', '@spawn', {
    check: (item) => assert(!item.additionalTextEdits?.length),
  });
  await has('fftw_using', 'using FFTW\nfunction run(tasks)\n return map(tasks) do task\n   At, _ = fetch(task)\n   abs2.(ff│(At))\n end\nend', 'fft');
  await has('fftw_unimported', 'module Audit\nfft_power() = abs2.(fft│([1.0, 2.0]))\nend', 'fft', {
    check: (item, _result, doc) => importEdit(item, doc, 'fft', /^using FFTW: fft\r?\n$/),
  });
  await has('fftw_qualified', 'import FFTW\nabs2.(FFTW.ff│([1.0, 2.0]))', 'fft');
  await has('fftw_selective', 'using FFTW: ff│\n', 'fft');
  await has('nearby_name', 'function run(interaction_mode, interaction_coef, interaction_m1_list, u)\n  x = [\n @. interaction_coef * (u == interaction_mode) + interaction_m1\n  for intera│\n  ]\nend', 'interaction_m1', {
    check: (item, result) => {
      assert.equal(asItems(result)[0].label, item.label);
      assert(!asItems(result).some((other) => other.label === 'interaction_mode'));
    },
  });
  const julia = process.env.JULIA_EXECUTABLE || 'julia';
  // Validate the child process environment before running the applied edits.
  // Julia uses ';' for LOAD_PATH on Windows and ':' on Unix.
  const fixture = '@assert Base.identify_package("Dagger") !== nothing\n' + autoImportPrograms.join('\n') + '\nusing FFTW\n@assert fft([1.0, 2.0]) ≈ ComplexF64[3, -1]\n';
  const evalResult = spawnSync(julia, ['--startup-file=no', '--compiled-modules=existing', `--project=${project}`, '-e', fixture], {
    cwd: project, encoding: 'utf8', timeout: 300_000,
    env: {...process.env, JULIA_LOAD_PATH: juliaLoadPath},
  });
  assert.equal(evalResult.status, 0, `${evalResult.error || ''}\n${evalResult.stderr}`);
  console.log('Julia accepted the actual edits, executed Dagger task and computed FFT');
  await request('shutdown', null);
  send({method: 'exit'});
} finally {
  child.kill();
}
