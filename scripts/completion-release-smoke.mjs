// Exercise the binary through stdio and real, pinned Julia package sources.
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { resolve, join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { setTimeout as pause } from 'node:timers/promises';

const [binary, project] = process.argv.slice(2).map(x => resolve(x));
assert(binary && project && existsSync(join(project, 'Project.toml')));
const root = pathToFileURL(project).href;
const child = spawn(binary, ['--no-config', 'lsp'], {
  cwd: project,
  env: { ...process.env, JULIA_LOAD_PATH: '@:@stdlib' },
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
  const caps = await request('initialize', {
    processId: process.pid, rootUri: root,
    workspaceFolders: [{ uri: root, name: 'release-smoke' }],
    capabilities: { general: { positionEncodings: ['utf-16'] } },
  });
  assert(caps.capabilities.completionProvider);
  send({ method: 'initialized', params: {} });

  await has('first_type', 'At_in::Vec│ = data[\nBt_in = 0\n', 'Vector');
  // Observe actual indexed dependency readiness, not initialize alone.
  await has('ready', 'using CSV: Fi│\n', 'File', { retry: true });
  await has('http_parent', 'import HTTP\nHTTP.Req│\n', 'Request');
  await has('http_function', 'import HTTP\nHTTP.ser│\n', 'serve!');
  await has('static_parent', 'import StaticArrays\nStaticArrays.SVe│\n', 'SVector');
  await has('ordered_select', 'import DataStructures: Ord│\n', 'OrderedDict');
  await has('macro_reexport', 'import DataFramesMeta: @ch│\n', '@chain');
  await has('distribution_from_loop', 'using Distributions: No│\n', 'Normal');
  await has('type_generated_by_macro', 'using StatsBase: We│\n', 'Weights');
  await has('relative_module', 'module Audit\nimport StaticArrays\nusing .Sta│\nend\n', 'StaticArrays');
  await has('relative_select', 'module Audit\nimport StaticArrays\nusing .StaticArrays: SVe│\nend\n', 'SVector');
  await has('module_self_selector', 'import Pluto: Pl│, ServerSession\n', 'Pluto');
  await has('module_self_usable', 'import Pluto: Pluto\nPluto.SessionActions.op│\n', 'open');
  await has('field_binder_shadow', 'import Pluto\nstruct Audit\n    Pluto::Pluto.Configuration.Opt│ions\nend\n', 'Options');
  await has('typed_field', 'import HTTP\nfunction audit(req::HTTP.Messages.Request)\n    req.tar│\nend\n', 'target');
  await has('typed_field_chain', 'struct Leaf\n    data::Float64\nend\nstruct Node\n    leaf::Leaf\nend\nfunction audit(n::Node)\n    n.leaf.da│\nend\n', 'data');
  await has('typed_external_facade_constructor', 'import HTTP\nfunction audit()\n    uri = HTTP.URI("/test")\n    uri.pa│\nend\n', 'path');
  await has('leafsize_keyword', 'using NearestNeighbors\nKDTree(coords; leaf│size = 10)\n', 'leafsize=', {
    check: item => assert.equal(item.textEdit?.newText, 'leafsize', 'Do not insert a second equals sign'),
  });
  await has('module_auto_import_csv', 'module Audit\nx = CSV.Fi│\nend\n', 'File', {
    check: (item, _, doc) => importEdit(item, doc, 'Fi', /\b(?:import|using) CSV\b/),
  });
  await has('module_auto_import_dataframe', 'module Audit\nx = DataFr│\nend\n', 'DataFrame', {
    check: (item, _, doc) => importEdit(item, doc, 'DataFr', /\b(?:import|using) DataFrames\b/),
  });
  if (process.env.JULIA_BINDIR) {
    const julia = join(process.env.JULIA_BINDIR, process.platform === 'win32' ? 'julia.exe' : 'julia');
    const run = spawnSync(julia, ['--startup-file=no', '--compiled-modules=existing', '-O0',
      `--project=${project}`, '-e', 'include_string(Main, read(stdin, String)); @assert isdefined(Audit1,:x) && isdefined(Audit2,:x)'], {
        input: autoImportPrograms.join('\n') + '\n', encoding: 'utf8', timeout: 240_000,
      });
    assert.equal(run.status, 0, `Julia could not execute the applied edits: ${run.stderr || run.error}`);
    console.log('Applied both edits and executed them in Julia');
  }
  await request('shutdown', null);
  send({ method: 'exit' });
  child.stdin.end();
} catch (error) {
  console.error(error);
  process.exitCode = 1;
} finally {
  if (!child.killed) child.kill();
}
