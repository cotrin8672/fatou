# Driver for :FatouCompilerHintsWatch. Restrict this distributed example to
# its own fixture, even though the editor supplies the current filename.
include("bridge.jl")
using .FatouCompilerSnapshot
module CompilerHintFixture end
source = realpath(only(ARGS))
source == realpath(joinpath(@__DIR__, "fixture.jl")) || error("expected bundled fixture.jl")
receipt = load_trusted!(CompilerHintFixture, source)
export_snapshot(stdout, receipt, CompilerHintFixture.callers, Tuple{})
