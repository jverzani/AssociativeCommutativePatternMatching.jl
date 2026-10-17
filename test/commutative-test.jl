## Tests of the commutative matcher, `_ceachmatch` (formerly CommutativePatternMatching)

using AssociativeCommutativePatternMatching
using Test

const CPM = AssociativeCommutativePatternMatching

include("commutative/backends.jl")
include("commutative/helpers.jl")
include("commutative/shared_tests.jl")
include("commutative/backend_tests.jl")
include("commutative/guard_tests.jl")
include("commutative/rule_tests.jl")

@testset "commutative matching" begin
    @testset "$B" for B ∈ BACKENDS
        shared_tests(B)
    end
    backend_tests()
    invert_tests()
    guard_tests()
    rule_tests()
    acrule_tests()
end
