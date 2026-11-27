# Standard driver used only after Neovim obtains explicit approval. It loads
# the saved source (ordinary Julia execution) and only reflects on the chosen
# specialization. It does not eval requested function/type expressions.
include("bridge.jl")
using .FatouCompilerSnapshot
module FatouWatchTarget end

function binding(scope::Module, name::Symbol)
    isdefined(scope, name) || throw(ArgumentError("unknown binding: $name"))
    getfield(scope, name)
end

function resolve_path(scope::Module, form)
    form isa Symbol && return binding(scope, form)
    if form isa Expr && form.head === :. && length(form.args) == 2 &&
        form.args[2] isa QuoteNode && form.args[2].value isa Symbol
        parent = resolve_path(scope, form.args[1])
        parent isa Module || throw(ArgumentError("qualification must name a module"))
        return binding(parent, form.args[2].value)
    end
    throw(ArgumentError("expected a simple or module-qualified name"))
end

function signature_arg(scope::Module, form)
    if form isa Expr && form.head === :curly && !isempty(form.args)
        owner = resolve_path(scope, form.args[1])
        owner isa Type || throw(ArgumentError("type parameters require a type constructor"))
        # Core.apply_type only builds a type; it does not invoke the constructor
        # or evaluate arbitrary Julia expressions.
        return Core.apply_type(owner, map(arg -> signature_arg(scope, arg), form.args[2:end])...)
    end
    form isa Int && return form
    form isa QuoteNode && form.value isa Symbol && return form.value
    leaf = resolve_path(scope, form)
    leaf isa Type || throw(ArgumentError("argument signature must contain types"))
    leaf
end

length(ARGS) == 3 || error("expected source file, function name and argument Tuple type")
file, name, type_tuple = ARGS
name_form = Meta.parse(name)
type_form = Meta.parse(type_tuple)
receipt, f, sig = redirect_stdout(stderr) do
    r = load_trusted!(FatouWatchTarget, file)
    Base.invokelatest() do
        owner = if name_form isa Expr && name_form.head === :.
            resolve_path(FatouWatchTarget, name_form.args[1])
        else
            FatouWatchTarget
        end
        owner isa Module || throw(ArgumentError("function owner must be a module"))
        value = resolve_path(FatouWatchTarget, name_form)
        value isa Function || throw(ArgumentError("selected binding is not a function"))
        tsig = signature_arg(owner, type_form)
        tsig isa Type && tsig <: Tuple || throw(ArgumentError("expected Tuple{...}"))
        r, value, tsig
    end
end
# Keep compiler/loaded-code stdout off of the editor connection as well.
report = IOBuffer()
redirect_stdout(stderr) do
    export_snapshot(report, receipt, f, sig)
end
write(stdout, take!(report))
