module FatouCompilerSnapshot

export load_trusted!, export_snapshot

const MAX_SOURCE_BYTES = 1_048_576
const MAX_HINTS = 256

struct LoadedSource
    path::String
    text::String
    first_world::UInt
    last_world::UInt
end

"""
Explicitly evaluate a trusted file, exactly once, in `mod` and record the
exact bytes passed to Julia. This is an ordinary Julia source-load action,
not a sandbox. Fatou never calls it. Do not use it on an untrusted file.
"""
function load_trusted!(mod::Module, path::AbstractString)
    file = realpath(path)
    text = open(file, "r") do io
        String(read(io, MAX_SOURCE_BYTES + 1))
    end
    isvalid(text) && ncodeunits(text) <= MAX_SOURCE_BYTES ||
        throw(ArgumentError("source is not bounded UTF-8"))
    before = Base.get_world_counter()
    Base.include_string(mod, text, file)
    LoadedSource(file, text, before, Base.get_world_counter())
end

# JSON subset for wire-only, non-executable compiler records. No package install.
function json(io, s::AbstractString)
    print(io, '"')
    for c in s
        if c == '"'
            print(io, "\\\"")
        elseif c == '\\'
            print(io, "\\\\")
        elseif UInt32(c) < 0x20
            print(io, "\\u", string(UInt32(c), base=16, pad=4))
        else
            print(io, c)
        end
    end
    print(io, '"')
end
json(io, n::Int) = print(io, n)
function json(io, a::AbstractVector)
    print(io, '[')
    for (i, value) in enumerate(a)
        i>1 && print(io, ',')
        json(io, value)
    end
    print(io, ']')
end
function json(io, x::NamedTuple)
    print(io, '{')
    for (i, (key,value)) in enumerate(pairs(x))
        i>1 && print(io, ',')
        json(io, String(key)); print(io, ':'); json(io, value)
    end
    print(io, '}')
end

function record(line, offset, sub, t, kind)
    start = offset + first(sub) - 1
    anchor = String(collect(codeunits(line)[sub]))
    (; startByte=start, endByte=start+ncodeunits(anchor), anchor,
        inferredType=sprint(show, t), kind)
end

function types_for(receipt::LoadedSource, f, sig::Type{<:Tuple})
    VERSION == v"1.13.4" ||
        throw(ArgumentError("this example is pinned to Julia 1.13.4 CodeInfo provenance"))
    isconcretetype(sig) || throw(ArgumentError("choose a concrete argument tuple"))
    current = Base.get_world_counter()
    m = which(f, sig)
    if String(m.file) != receipt.path || !(receipt.first_world < m.primary_world <= receipt.last_world)
        throw(ArgumentError("method was not defined by the recorded source load or was replaced"))
    end
    ci, ret = only(Base.code_typed(f, sig; optimize=false, debuginfo=:source, world=current))
    ci isa Core.CodeInfo || throw(ArgumentError("compiler returned no typed IR"))
    current == Base.get_world_counter() || throw(ArgumentError("Julia world changed during inference"))
    lines = split(receipt.text,'\n')
    offsets = accumulate(+, [0; [ncodeunits(line)+1 for line in lines]])
    entries = NamedTuple[]
    for (i, stmt) in pairs(ci.code)
        stmt isa Expr && stmt.head === :(=) && stmt.args[1] isa Core.SlotNumber || continue
        name = ci.slotnames[stmt.args[1].id]
        count(==(name), ci.slotnames) == 1 || continue
        stack = Base.IRShow.buildLineInfoNode(ci.debuginfo, m, i)
        length(stack) == 1 && String(stack[1].file) == receipt.path || continue
        ln = Int(stack[1].line)
        1 <= ln <= length(lines) || continue
        line = lines[ln]
        parsed = Meta.parse(line; raise=false)
        parsed isa Expr && parsed.head === :(=) && parsed.args[1] === name || continue
        span = match(r"^(\s*)([\p{L}_][\p{L}\p{N}_!]*)\s*=", line)
        span === nothing && continue
        n = ncodeunits(span[1])
        lattice = ci.ssavaluetypes[i]
        t = lattice isa Core.Const ? typeof(lattice.val) : lattice
        t isa Type || continue
        push!(entries, record(line,offsets[ln], n+1:n+ncodeunits(span[2]), t, "assignment"))
    end
    # No duplicate hint next to a written return annotation, multiline or macro
    # signature. Establish file and definition line from the actual method.
    l = lines[Int(m.line)]
    header = match(r"^\s*function ([\p{L}_][\p{L}\p{N}_!]*)\([^()]*\)\s*$", l)
    if header !== nothing && Symbol(header[1]) === m.name && ret isa Type
        i = findlast(==(')'), l)
        push!(entries, record(l, offsets[m.line], i:i, ret, "return"))
    end
    # Ambiguous same-source-position entries are never emitted.
    counts = Dict{Int,Int}()
    for entry in entries
        counts[entry.endByte] = get(counts,entry.endByte,0) + 1
    end
    filter!(entry -> counts[entry.endByte]==1, entries)
    length(entries)<=MAX_HINTS || throw(ArgumentError("too many compiler hints"))
    signature = string(m.module, ".", m.name, " ", sig)
    (; source=receipt.text, sourcePath=receipt.path, juliaVersion=string(VERSION), world=string(current), signature, hints=entries)
end

"""
Export a data-only snapshot for one verified loaded method specialization.
Compiler reflection may execute generated functions. Only use this explicit
action in a session and environment you trust. No evaluation of CLI/editor
strings takes place during export. Source gets sent only to the local LSP
client you explicitly import it into.
"""
function export_snapshot(io::IO, receipt::LoadedSource, f, sig::Type{<:Tuple})
    json(io, types_for(receipt,f,sig))
    println(io)
end
end # module
