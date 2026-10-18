## Backend-specific tests: behavior that depends on how a subject is stored

function backend_tests()
    @testset "Expr (no canonicalization)" begin
        # terms are not combined or rewritten
        @test binds(matchone(:(~x + ~x), :(a + a)), :x => :a)
        @test matchone(:(~x + ~x), :(a + b)) === nothing
        @test binds(matchone(:(~x - ~y), :(a - b)), :x => :a, :y => :b)

        # no associativity: a nested sum has two arguments
        sub = Expr(:call, :+, :(a + b), :c)
        σs = eachm(:(~x + ~y), sub)
        @test length(σs) == 2
        @test has_match(σs, :x => :(a + b), :y => :c)

        # literal symbols in a pattern
        @test binds(matchone(:(x * sin(~y)), :(x * sin(a))), :y => :a)
        @test binds(matchone(:(f(~x)), :(f(a))), :x => :a)
        @test binds(matchone(:((~F)(~x)), :(f(a))), :F => :f, :x => :a)

        # segments in a non-commutative operation keep their order
        σ = matchone(:(f(~x, ~~y)), :(f(a, b, c)))
        @test σ[:x] == :a && collect(σ[:y]) == [:b, :c]
        # segments bind to tuples, as in the commutative case
        @test σ[:y] isa Tuple
        # with no other arguments, segments are filled greedily
        σs = eachm(:(f(~~x, ~~y)), :(f(a, b, c)))
        @test length(σs) == 1
        @test all(σ -> [σ[:x]..., σ[:y]...] == [:a, :b, :c], σs)
        @test isempty(eachm(:(f(~~~x, ~y, ~~~z)), :(f(a, b))))

        # guards on segments of a non-commutative operation
        @test binds(matchone(:(f(~x, ~~y::(u -> length(u) == 2))), :(f(a, b, c))),
                    :x => :a, :y => (:b, :c))
        @test matchone(:(f(~x, ~~y::(u -> length(u) == 1))), :(f(a, b, c))) === nothing
        @test binds(matchone(:((~F)(~~y::(u -> length(u) == 3))), :(f(a, b, c))),
                    :F => :f, :y => (:a, :b, :c))
        @test matchone(:((~F)(~~y::(u -> length(u) == 2))), :(f(a, b, c))) === nothing
    end

    @testset "$(B.name) (canonicalizing)" for B ∈ filter(B -> B.canonicalizes, BACKENDS)
        S = B.build

        # a + a is stored as 2a
        @test matchone(:(~x + ~x), S(:(a + a))) === nothing
        @test binds(matchone(:(~n * ~x), S(:(a + a))), :n => 2, :x => S(:a))

        # a - b is stored as a sum
        @test matchone(:(~x - ~y), S(:(a - b))) === nothing
        @test has_match(eachm(:(~x + ~y), S(:(a - b))), :x => S(:a), :y => S(:(-b)))

        # a power with a symbolic exponent is compared to 1//2 for `sqrt`
        # without `==`, which is not a Bool for SymbolicUtils
        @test matchone(:(sqrt(~x)), S(:(a ^ (2b)))) === nothing
        @test binds(matchone(:(sqrt(~x)), S(:(a ^ (1//2)))), :x => S(:a))

        # a quotient against a quotient, or its canonical form, as products of
        # powers: 1/(x * log(x)) is (log(x))^(-1) / x
        @test any(σ -> isequal(CPM.unwrap_const(σ[:p]), -1) && isequal(σ[:x], S(:x)) && isequal(σ[:u], S(:(log(x)))),
                  eachm(:((~u)^(~!p) / ~x), S(:(1 / (x * log(x))))))

        # a product of powers against a quotient with a product denominator
        @test has_match(eachm(:((~u)^(~m) * (~v)^(~n) * (~w)^(~!p)), S(:((x + 3) / ((x - 1) * (x + 1)^2)))),
                        :u => S(:(x - 1)), :m => -1, :v => S(:(x + 1)), :n => -2, :w => S(:(x + 3)), :p => 1)

        # a numeric factor in a quotient's denominator is inverted as a number
        q = S(:(1 / (2 * (x + 1))))
        if Symbol(operation(q)) === :/
            @test has_match(eachm(:((~u)^(~m) * ~c), q), :u => S(:(x + 1)), :m => -1, :c => 1//2)
        end

        # 1/sqrt(u) against u^(-1//2), as SimpleExpressions keeps it
        @test binds(matchone(:(1 / sqrt(~u)), S(:((a + b) ^ (-1//2)))), :u => S(:(a + b)))
    end
end

function invert_tests()
    @testset "rational in a denominator" begin
        # u / (3//2) is u * (2//3)
        @test binds(matchone(:(~u / (3//2)), :(x * (2//3))), :u => :x)
        S = backend("SymbolicUtils").build
        @test binds(matchone(:(~u / (3//2)), S(:(x * (2//3)))), :u => S(:x))
    end
end

# The associative-commutative matcher matches powers written differently as
# the commutative matcher does: when `_cmatch` matches, its match is among
# those of `_eachmatch` (up to the standard order).
function ac_powers_tests()
    cases = [
        (:((~u)^(~m)), :(1 / sqrt(x))),
        (:((~u)^(~m)), :(1 / x)),
        (:((~u)^(~m)), :(1 / x^2)),
        (:((~u)^(~m)), :(1 / exp(x))),
        (:((~u)^(~m)), :(exp(x))),
        (:((~u)^(~m)), :(sqrt(x))),
        (:(ℯ^(~n)), :(exp(x))),
        (:(sqrt(~u)), :(x^(1//2))),
        (:(1 / sqrt(~u)), :((a + b)^(-1//2))),
        (:((~u)^(~m) * ~v), :(a / b)),
        (:((~u)^(~m) * ~v), :(a / b^2)),
        (:((~u)^(~!p) / ~x), :(1 / (x * log(x)))),
        (:((~u)^(~m) * (~v)^(~n) * (~w)^(~!p)), :((x + 3) / ((x - 1) * (x + 1)^2))),
        (:((~u)^(~m) * ~c), :(1 / (2 * (x + 1)))),
    ]
    _std(x) = x isa Expr ? CPM._canonical(x) : x
    agree(σ, σ′) = issetequal(keys(σ), keys(σ′)) &&
        all(k -> same(_std(σ[k]), _std(σ′[k])), keys(σ))
    @testset "powers written differently, _match ($(B.name))" for B ∈ BACKENDS
        for (pat, sub) ∈ cases
            S = B.build(sub)
            σc = CPM._cmatch(pat, S)
            σc === nothing && continue # e.g. SimpleExpressions stores 1/(2x + 2)
            @test any(σ -> agree(σ, σc), CPM._eachmatch(pat, S))
        end
        # a guard is checked on the exponent of the rewritten subject
        @test CPM._match(:((~x)^(~n::(!=(-1)))), B.build(:(1 / x))) === nothing
    end
end

# The associative-commutative matcher on symbolic subjects: arguments are
# compared with `isequal`, as `==` may not give a Bool, and are picked out
# without indexing by a vector, which SymbolicUtils' arguments do not allow.
function ac_symbolic_tests()
    @testset "_match on terms ($(B.name))" for B ∈ BACKENDS
        S = B.build
        @test binds(CPM._match(:(sin(~x) * cos(~x)), S(:(sin(t) * cos(t)))), :x => S(:t))
        @test binds(CPM._match(:(~x * sin(~x)), S(:(x * sin(x)))), :x => S(:x))
        @test binds(CPM._match(:(sin(~x)^2 + cos(~x)^2), S(:(sin(t)^2 + cos(t)^2))), :x => S(:t))
        @test CPM._match(:(sin(~x) + cos(~y)), S(:(cos(a) + sin(b)))) !== nothing
        @test length(collect(CPM._eachmatch(:((~x)^2 + (~y)^2), S(:(a^2 + b^2))))) == 2
        @test CPM._match(:(~x * (~!a + ~!b * ~x)^(~!m)), S(:(x * (2 + 3x)^4))) !== nothing
    end
end
