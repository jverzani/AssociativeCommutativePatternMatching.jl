using Test
using AssociativeCommutativePatternMatching
using AssociativeCommutativePatternMatching: _eachmatch, _replace, _match


include("match-test.jl")
include("matchpy-test.jl")
# run JET before the commutative tests load symbolic packages, whose methods (e.g. for `enumerate`) confuse its analysis
VERSION >= v"1.12" && include("test-jet.jl")
include("commutative-test.jl")
