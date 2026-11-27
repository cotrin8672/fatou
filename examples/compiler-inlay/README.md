# Opt-in Julia compiler snapshot inlay hints

This is an experimental example; Fatou never launches Julia or loads your
workspace to obtain a hint. Until an explicit import, Julia source gets no
type hints from this provider. The existing Project TOML hints are unchanged.

1. With Julia 1.13.4, run the **trusted example**:
   ```sh
   julia --startup-file=no examples/compiler-inlay/demo.jl > compiler-hints.json
   ```
   The bridge explicitly evaluates the fixture once, captures the bytes loaded
   by Julia, then uses the compiler's typed IR at the selected signature. On
   PowerShell, ensure the report is UTF-8 if redirecting stdout; alternatively
   use Julia's `open` with write mode as below.
2. Open the exact `examples/compiler-inlay/fixture.jl` file using the Fatou
   prototype. Do not copy it to a different path. In **Neovim 0.11+**, use
   `:luafile /absolute/path/to/examples/compiler-inlay/nvim.lua` to add two
   commands for this session only (no configuration file is edited).
3. Run `:FatouCompilerHintsImport /absolute/path/to/compiler-hints.json`.
   A successful import enables standard inlay rendering for this buffer only.
   `:FatouCompilerHintsClear` discards the report. Other editors can send the
   same small JSON-RPC sequence below.

For your own trusted code, deliberately load a file into a Julia module using
`FatouCompilerSnapshot.load_trusted!` and save its receipt. Then choose a
concrete argument signature explicitly. The selected method must still be
the one defined by that exact source load:
```julia
open("compiler-hints.json", "w") do io
    export_snapshot(io, receipt, MyModule.solve, Tuple{Vector{Float64}})
end
```
Do not load an untrusted file or reflect on untrusted call targets. Julia
compile-time code, including generated functions, can execute during reflection.
Fatou does not discover, load, evaluate or send a report anywhere on its own.
The JSON includes the full source text; keep the artifact private.

### Protocol

A trusted client sends the custom request `fatou/compilerHintsTarget` with
`{"uri":"file:///..."}`. The server replies with the current open document's
`version` and a one-use `ticket`. Immediately send
`fatou/compilerHintsImport` with `{uri,version,ticket,snapshot}`; its snapshot
is the exact report in the file above. A successful request returns
`{"imported": N}`. The server verifies exact source path and bytes, anchor
byte ranges, document identity/version, and limits (1 MiB source, 256 hints).
It never uses these parameters to read the filesystem or execute anything.
Then use ordinary `textDocument/inlayHint`. Clients can request
`fatou/compilerHintsClear` to remove the loaded snapshot. Fatou requests an
inlay refresh only if the client advertises support.

### Scope

- **Compiler snapshot of one explicit specialization**, not the declared
  generic type. The tooltip records signature, Julia version and world at
  export; an inference result is not an observation of runtime values.
  JETLS can analyze declared signatures and far more expressions using its
  own compiler context/lowering; this small bridge doesn't infer methods at
  `Any` or choose a specialization for you.
- The bridge shows verified direct single-line assignments and a verified
  simple function return label. It does not add edits or duplicate declared
  return annotations. A compiler result of `Any` indicates no narrower
  inferred answer for this signature; an absent or unmapped result emits
  no hint. `Union{}` explains no normal return, not necessarily a throw.
  Small unions such as `Union{Nothing, Int64}` are displayed without warnings.
  To reduce noise, clear the current report or disable inlays for that buffer;
  there is no separate type filter in this prototype. Long labels are
  shortened, with full types in tooltips.
  Macro-generated spans, incomplete syntax, nested ambiguous provenance and
  unknown cases are omitted rather than guessed.
- Editing, closing, saving, or a watched/environment change invalidates the
  in-memory report or ticket. A terminal's Julia world cannot be monitored by
  this offline file transfer: clear/re-export/import after interactive
  changes or a restart. It is a clearly dated-to-world snapshot, not live
  Julia state across processes. Windows/UNC path conversion uses Fatou's
  existing codec; alternate path spelling or symlinks may fail closed.
