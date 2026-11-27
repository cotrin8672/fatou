include("bridge.jl")
using .FatouCompilerSnapshot
module CompilerHintFixture end
receipt = load_trusted!(CompilerHintFixture, joinpath(@__DIR__, "fixture.jl"))
choice = isempty(ARGS) ? "callers" : only(ARGS)
if choice == "callers"
    export_snapshot(stdout, receipt, CompilerHintFixture.callers, Tuple{})
elseif choice == "any"
    export_snapshot(stdout, receipt, CompilerHintFixture.any_input, Tuple{Vector{Any}})
elseif choice == "bottom"
    export_snapshot(stdout, receipt, CompilerHintFixture.no_normal_return, Tuple{})
elseif choice == "optional"
    export_snapshot(stdout, receipt, CompilerHintFixture.maybe_none, Tuple{Bool})
else
    error("choose a trusted fixture name: callers, any, bottom, optional")
end
