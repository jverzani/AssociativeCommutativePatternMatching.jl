using Test
using AssociativeCommutativePatternMatching
import AssociativeCommutativePatternMatching: _match, _eachmatch

function AssociativeCommutativePatternMatching.isassociative(x::Symbol)
    x ∈ (:(+), :(*)) && return true
    nm = string(x)
    endswith(nm, "ₐ") && return true
    endswith(nm, "ₐₘ") && return true
    false
end

function AssociativeCommutativePatternMatching.iscommutative(x::Symbol)
    x ∈ (:(+), :(*)) && return true
    nm = string(x)
    endswith(nm, "ₘ") && return true
    false
end


## -- test internal functions
@testset "syntactic_match" begin
    pat, sub = :(cos(sin(a))), :(cos(sin(a)))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test m == AssociativeCommutativePatternMatching.MatchDict()

    pat, sub = :(sin(~x)), :(sin(2x + cos(x)))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test m[:x] == :(2x + cos(x))

    pat, sub = :(F(sin(~x), ~x)), :(F(sin(2x), 2x))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test m[:x] == :(2x)

    pat, sub = :(cos(sin(a))), :(cos(sin(b)))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test isnothing(m)

    pat, sub = :(sin(cos(a))), :(cos(a))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test isnothing(m)

    pat = :((~F)(~x, ~y))
    sub = :(g(a,b))
    m = AssociativeCommutativePatternMatching.syntactic_match(sub, pat)
    @test length(m) == 3
    @test m[:F] == :g


end

@testset "associative" begin
    sub = :(1 + a + b)
    pat = :(1 + (~x))
    θ = AssociativeCommutativePatternMatching.match_one_to_one((sub,), pat)
    @test length(collect(θ)) == 1
    σ = only(θ)
    @test σ[:x] == :(a + b)

    θ = AssociativeCommutativePatternMatching.match_one_to_one((:(a + b + c),), :((~~~x) + (~~~y)))
    @test length(collect(θ)) == 6 # (c, a+b),(a,c+b),(b,c+a),(c+a,b),(c+b,a), (a+b,c)

    # match
    # should not match
    sub = :(log(1 + (x^2/2 - x^4/24)))
    @test !isnothing(_match(:(log(1 + ~x)), sub))
    @test !isnothing(_match(:(log(1 + (~~~x))), sub)) # again (~x) like (~~~x)

end

@testset "constant patterns" begin
    @test isempty(AssociativeCommutativePatternMatching.match_sequence((:a,:b,:c), (:a,:b,:b)))    # no substitutions
    @test only(AssociativeCommutativePatternMatching.match_sequence((:a,:b,:c), (:a,:b,:c))) == AssociativeCommutativePatternMatching.MatchDict() # one trivial substitution
end

@testset "matched variables" begin

    ss, ps = [:a,:b,:c], [:(~x),:(~y),:(~z)]
    σ₀ = AssociativeCommutativePatternMatching.match_dict()
    σ = AssociativeCommutativePatternMatching.match_dict(:x => :a)

    ss′, ps′ = AssociativeCommutativePatternMatching._match_matched_variables(ss, ps, σ)
    @test ss′ == [:b,:c] && ps′ == [:(~y),:(~z)]


    Θ = AssociativeCommutativePatternMatching.match_commutative_sequence(ss, ps, nothing, (σ₀,))
    @test length(collect(Θ)) == 6

    Θ = AssociativeCommutativePatternMatching.match_commutative_sequence(ss, ps, nothing, (σ,))
    @test length(collect(Θ)) == 2
end


@testset "non-variable" begin
    pat =:(fₘ(g(a,(~x)), g((~x),(~y)), g((~~~z))))
    sub = :(fₘ(g(a,b), g(b,a), g(a,c)))
    θ = AssociativeCommutativePatternMatching.match_one_to_one((sub,), pat)
    σ = only(θ)
    @test length(σ) == 3
    @test σ[:x] == :b && σ[:y] == :a && σ[:z] == [:a, :c]

end

@testset "regular variables" begin
    sub = :(fₘ(a,a,a,b,b,c))
    pat = :(fₘ((~x),(~x),(~~y)))
    θ = AssociativeCommutativePatternMatching.match_one_to_one((sub,), pat)
    @test length(collect(θ)) == 2

    sub = :(fₐₘ(a,a,a,b,b,c))
    pat = :(fₐₘ((~x),(~x),(~~y))) # associative has (~x) like (~~~x)
    θ = AssociativeCommutativePatternMatching.match_one_to_one((sub,), pat)
    @test length(collect(θ)) == 3 # ((~x) => fₐₘ(a, b), (~~y) => fₐₘ(a, c))

end

@testset "sequence variables" begin

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~~x), :(~~~y)])
    @test length(collect(θ)) == 2 # u(a,b), u(c); u(a), u(b,c)

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~~x), :(~~y)], :u)
    @test length(collect(θ)) == 3 # add u(a,b,c),u()

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~x), :(~~y)], :u)
    @test length(collect(θ)) == 4


    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~~x), :(~~~y)], :(uₘ)) # are these right
    @test length(collect(θ)) == 2 #

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~~x), :(~~y)], :(uₘ))
    @test length(collect(θ)) == 3

    θ = AssociativeCommutativePatternMatching.match_sequence([:a,:b,:c], [:(~~x), :(~~y)], :(uₐₘ))
    @test length(collect(θ)) == 4


end

@testset "correctness: matching edge cases" begin
    ms(pat, sub) = collect(_eachmatch(pat, sub))

    # constant patterns remove only one copy from the subject
    θ = ms(:(a + ~x), :(a + a + b))
    @test length(θ) == 1 && only(θ)[:x] == :(a + b)
    θ = ms(:(2 * ~x), :(2 * 2 * y))
    @test length(θ) == 1 && only(θ)[:x] == :(2 * y)
    @test isempty(ms(:(a + a + ~x), :(a + b + c)))

    # non-variable patterns keep repeated leftover terms, without duplicate matches
    θ = ms(:(g(~y) + ~~z), :(g(c) + a + a))
    @test length(θ) == 1 && only(θ)[:y] == :c && only(θ)[:z] == [:a, :a]
    θ = ms(:(g(~y) + ~~z), :(g(a) + g(a) + b))
    @test length(θ) == 1 && only(θ)[:y] == :a && only(θ)[:z] == [:b, :(g(a))]

    # star variables may match nothing in a commutative function
    θ = ms(:(fₘ(a, ~~z)), :(fₘ(a)))
    @test length(θ) == 1 && only(θ)[:z] == []
    θ = ms(:(fₘ(~x, ~~z)), :(fₘ(a)))
    @test length(θ) == 1 && only(θ)[:x] == :a && only(θ)[:z] == []
    @test isempty(ms(:(fₘ(a, ~~~z)), :(fₘ(a))))  # plus variables still need a term

    # guards on regular variables in commutative, non-associative functions
    @test isempty(ms(:(fₘ(~x::isodd, ~y)), :(fₘ(2, 4))))
    θ = ms(:(fₘ(~x::isodd, ~y)), :(fₘ(2, 3)))
    @test length(θ) == 1 && only(θ)[:x] == 3 && only(θ)[:y] == 2

    # a variable bound to a sum is found within a flattened associative subject
    θ = ms(:(f(~x, ~x + ~y)), :(f(a + b, a + b + c)))
    @test length(θ) == 1 && only(θ)[:x] == :(a + b) && only(θ)[:y] == :c
    @test isempty(ms(:(f(~x, ~x + ~y)), :(f(a + b, a + c))))

    # same variable with and without a guard is a non-match, not an error
    @test isempty(ms(:(fₘ(~x::isodd, ~x)), :(fₘ(3, 5))))
    θ = ms(:(fₘ(~x::isodd, ~x)), :(fₘ(3, 3)))
    @test length(θ) == 1 && only(θ)[:x] == 3

    # default exponent on a literal base
    σ = _match(:(x^(~!n)), :x)
    @test !isnothing(σ) && σ[:n] == 1

    # normalizing 1/u^v against a negative power
    σ = _match(:(1/(~x)^2), :(a^(-2)))
    @test !isnothing(σ) && σ[:x] == :a
    @test isempty(ms(:(1/(~x)^(~n)), :(a^(-2)))) # symbolic exponent: no match, no error

    # ℯ^x pattern matches exp(x)
    σ = _match(:(ℯ^(~x)), :(exp(y)))
    @test !isnothing(σ) && σ[:x] == :y

    # inverting a rational
    @test AssociativeCommutativePatternMatching._invert_expr(:(1//2)) == :(2//1)
    @test AssociativeCommutativePatternMatching._invert_expr(2) == :(2^-1)
    σ = _match(:((~x)/2), :(y * 2^-1))  # pattern normalized to (~x) * 2^-1
    @test !isnothing(σ) && σ[:x] == :y
end

@testset "default slots: fewest defaults" begin
    ms(pat, sub) = collect(_eachmatch(pat, sub))
    @test collect(AssociativeCommutativePatternMatching.powerset(1:3)) ==
        sort(collect(AssociativeCommutativePatternMatching.powerset(1:3)), by=length) # assumed ordering

    # all matches using the fewest defaults, independent of argument order
    θ = ms(:(~!a + ~!b), :y)
    @test Set((σ[:a], σ[:b]) for σ ∈ θ) == Set([(0, :y), (:y, 0)])
    θ = ms(:(~!b + ~!a), :y)
    @test Set((σ[:a], σ[:b]) for σ ∈ θ) == Set([(0, :y), (:y, 0)])

    # fewer defaults preferred
    θ = ms(:((~!a) * (~x)^(~!n)), :(y^2))
    @test length(θ) == 1 && only(θ)[:a] == 1 && only(θ)[:x] == :y && only(θ)[:n] == 2
    θ = ms(:((~!a) * (~x)^(~!n)), :y)
    @test length(θ) == 1 && only(θ)[:a] == 1 && only(θ)[:x] == :y && only(θ)[:n] == 1

    # default exponent is not used when the base would match a power
    @test isempty(ms(:(f(~n, (~x)^(~!n))), :(f(1, y^3))))
    σ = _match(:(f(~n, (~x)^(~!n))), :(f(1, y)))
    @test !isnothing(σ) && σ[:x] == :y && σ[:n] == 1
end

@testset "default slots: guards" begin
    ms(pat, sub) = collect(_eachmatch(pat, sub))

    # guard kept when a default slot matches a term
    @test isempty(ms(:(~!a::isodd + ~!b::isodd), 2))
    θ = ms(:(~!a::isodd + ~!b::isodd), 3)
    @test Set((σ[:a], σ[:b]) for σ ∈ θ) == Set([(0, 3), (3, 0)])

    @test isempty(ms(:((~x)^(~!n::iseven)), :(y^3)))
    σ = _match(:((~x)^(~!n::iseven)), :(y^2))
    @test !isnothing(σ) && σ[:x] == :y && σ[:n] == 2
end

@testset "commutative arguments in standard order" begin
    ms(pat, sub) = collect(_eachmatch(pat, sub))

    # constant subterms equal up to commutativity
    θ = ms(:(sin(a + b) + ~x), :(sin(b + a) + c))
    @test length(θ) == 1 && only(θ)[:x] == :c
    @test isempty(ms(:(sin(a - b) + ~x), :(sin(b - a) + c)))   # - is not commutative
    σ = _match(:(f(~x, g(b * a))), :(f(1, g(a * b))))
    @test !isnothing(σ) && σ[:x] == 1
    @test !isnothing(_match(:(sin(a + b)), :(sin(b + a))))     # no wildcards
    @test isnothing(_match(:(sin(a - b)), :(sin(b - a))))

    # repeated variables compare equal up to commutativity
    σ = _match(:(f(~x, ~x)), :(f(a + b, b + a)))
    @test !isnothing(σ) && σ[:x] == :(a + b)
    @test isnothing(_match(:(f(~x, ~x)), :(f(a - b, b - a))))
end
