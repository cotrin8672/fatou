include("bridge.jl")
using .FatouCompilerSnapshot
module CompilerHintFixture end
infer(receipt, f, sig) = FatouCompilerSnapshot.types_for(receipt, f, sig)
receipt = load_trusted!(CompilerHintFixture, joinpath(@__DIR__, "fixture.jl"))

output = infer(receipt, CompilerHintFixture.callers, Tuple{})
@assert length(output.hints) == 5
@assert only(filter(x->x.kind=="return", output.hints)).inferredType ==
    "Tuple{Int64, Float64, Int64, Float64}"
@assert only(filter(x->x.anchor=="β",output.hints)).inferredType == "Float64"
@assert only(infer(receipt, CompilerHintFixture.scaled,Tuple{Int}).hints).inferredType == "Int64"
@assert only(infer(receipt, CompilerHintFixture.scaled,Tuple{Float64}).hints).inferredType == "Float64"
@assert only(infer(receipt, CompilerHintFixture.branch,Tuple{Bool}).hints).inferredType == "Union{Missing, Int64}"

@assert map(x->x.inferredType, infer(receipt, CompilerHintFixture.any_input,Tuple{Vector{Any}}).hints) == ["Any", "Any"]
@assert only(infer(receipt, CompilerHintFixture.no_normal_return,Tuple{}).hints).inferredType == "Union{}"
@assert only(infer(receipt, CompilerHintFixture.maybe_none,Tuple{Bool}).hints).inferredType == "Union{Nothing, Int64}"

# Unrelated definitions do not invalidate the exact method source receipt.
Core.eval(CompilerHintFixture, :(world_change_sentinel(x) = x))
@assert length(infer(receipt, CompilerHintFixture.callers,Tuple{}).hints) == 5
# A changed candidate cannot be attached to the old source receipt.
Core.eval(CompilerHintFixture, :(callers() = :replacement))
stale = try
    infer(receipt, CompilerHintFixture.callers,Tuple{})
    false
catch e
    e isa ArgumentError && occursin("recorded source load", string(e))
end
@assert stale
println("bridge: concrete specializations, Any, bottom, small Union, UTF-8 and stale world passed")
