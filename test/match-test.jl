using Test
using AssociativeCommutativePatternMatching
using AssociativeCommutativePatternMatching: _eachmatch, _replace, _match
using TermInterface

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



## ----
# Main user interface are methods for `replace`, `match`, `eachmatch`

@testset "_eachmatch" begin
    ts = [
        # single variables
        (pat = :(~x),
         sub = :(a + b + c),
         len = 1),
        (pat = :(~!x),
         sub = :(a + b + c),
         len = 1),
        (pat = :(~~x),
         sub = :(a + b + c),
         len = 1),
        (pat = :(~~~x),
         sub = :(a + b + c),
         len = 1),

        # multiple variables
        (pat = :(~x + ~y),
         sub = :(a + b + c),
         len = 6),
        (pat = :(~x + ~!y),
         sub = :(a),
         len = 1),
        (pat = :(~x + ~!y),
         sub = :(a + b + c),
         len = 6),
        (pat = :(~x + ~~y),
         sub = :(a + b + c),
         len = 7),
        (pat = :(~x + ~~~y),
         sub = :(a + b + c),
         len = 6),
        (pat = :(~!x + ~~y),
         sub = :(a + b + c),
         len = 7),
        (pat = :(~!x + ~~~y),
         sub = :(a + b + c),
         len = 6),
        (pat = :(~~x + ~~y),
         sub = :(a + b + c),
         len = 8),
        (pat = :(~~x + ~~~y),
         sub = :(a + b + c),
         len = 7),
        (pat = :(~~~x + ~~~y),
         sub = :(a + b + c),
         len = 6),

        # def slot with ^
        (pat = :((~x)^(~!y)),
         sub = :(a),
         len = 1),
        (pat = :((~x)^(~y)),
         sub = :(a),
         len = 0),
        (pat = :((~x)^(~!y)),
         sub = :(a^2),
         len = 1),
         (pat = :(~x + (~y)^(~!z)),
         sub = :(a + b),
         len = 2),
        (pat = :(~!x + (~y)^(~!z)),
         sub = :(a + b),
         len = 2),

        # defslot combos
        (pat = :((~!a)*(~x)),
         sub = :(x),
         len = 1),
        (pat = :((~!a)*(~x) + (~!b)),
         sub = :(x),
         len = 1),


        # wrapped in functions

        (pat = :(log(~x) + log(~y)),
         sub = :(log(a) + log(b)),
         len = 2),
        (pat = :(log(~x) + ~!y),
         sub = :(log(a) + log(b)),
         len = 2),
        (pat = :(log(~x) + log(~y) + log(~z)),
         sub = :(log(a) + log(b) + log(c)),
         len = 6),



        (pat = :(log(1 + ~x)),
         sub = :(log(1 + x^2)),
         len = 1),
        (pat = :(log(1 + ~x)),
         sub = :(log(1 + x) + log(1 + x^2)),
         len = 0),
        (pat = :(log(1 + ~x) + ~!y),
         sub = :(log(1 + x) + log(1 + x^2)),
         len = 2),


        (pat = :(log(log(~~~x + ~~~y))),
         sub = :(log(log(a + b + c))),
         len = 6),
        (pat = :(log(log(~~~x + ~!y))),
         sub = :(log(log(a + b + c))),
         len = 6),
        (pat = :(~!x + log(log(~y))),
         sub = :(log(log(a)) + log(log(b))),
         len = 2),

        # single argument
        (pat = :(f(~x)),
         sub = :(f(a,b,c)),
         len = 0),
        (pat = :(fₐ(~x)),
         sub = :(fₐ(a,b,c)), # associative matches MP, not R2
         len = 1),
        (pat = :(fₐₘ(~x)),   # associative matches MP, not R2
         sub = :(fₐₘ(a,b,c)),
         len = 1),
        (pat = :(fₘ(~x)),
         sub = :(fₘ(a,b,c)),
         len = 0),
        (pat = :(fₘ(~x, ~y)),
         sub = :(fₘ(a, b)),
         len = 2),

        # multiple
        (pat = :(f(~~~x, ~~~y)),
         sub = :(f(a,b,c)),
         len = 2),
        (pat = :(f(~~x, ~~y)),
         sub = :(f(a,b,c)),
         len = 4),
        (pat = :(fₐ(~~~x, ~~~y)),
         sub = :(fₐ(a,b,c)),
         len = 2),
        (pat = :(fₐ(~~x, ~~y)),
         sub = :(fₐ(a,b,c)),
         len = 4),
        (pat = :(fₐₘ(~~~x, ~~~y)),
         sub = :(fₐₘ(a,b,c)),
         len = 6),
        (pat = :(fₐₘ(~~x, ~~y)),
         sub = :(fₐₘ(a,b,c)),
         len = 8),

        (pat = :(exp(~y) + exp(~x)),
         sub = :(exp(y) + exp(x)),
         len = 2),
        (pat = :(*(~a, ~~x) + *(~b,~~x)),
         sub = :(2x + 3*x*y),
         len = 4),
        (pat = :((~!a)*sin(~x) ^ 2 + (~!a)*cos(~x) ^ 2),
         sub =  :(sin(2x) ^ 2 + cos(2x) ^ 2),
         len = 1),
        (pat = :((~!a)*sin(~x) ^ 2 + (~!a)*cos(~x) ^ 2),
         sub =  :(x*sin(2x) ^ 2 + x*cos(2x) ^ 2),
         len = 1),
        (pat = :((~x)^(~!m) * (~x)^(~!n)),
         sub = :(x^2 * x^3),
         len = 2),
        (pat = :(~!a * sin(~!b *~x + ~!c)^(~!m)),
         sub = :(sin(2x)),
         len = 2),

        # function head
        (pat = :((~F)(~x, ~y)),
         sub = :(g(a, b)),
         len = 1),
        (pat = :((~F)(~x, ~~y)),
         sub = :(g(a, b,c)),
         len = 1),

        # integral matches from SymbolicIntegration.jl rules
        (pat = :(∫((~(!c) + ~(!d) * ~x) ^ ~(!m) * sin(~(!e) + (~(!f) * ~x) / 2) ^ 2, ~x)),
         sub = :(∫((a + b*y)^2 * sin(c + d*y/2)^2, y)),
         len = 1),
        (pat = :(∫((~!u)*((~!a)*(~x)^(~n))^(~m),(~x)) ),
         sub = :(∫(a*(x^b)^c ,x)),
         len = 1),
        (pat = :(∫((~!u)*((~!c)*((~!d)*((~!a) + (~!b)* (~x))^(~n))^(~q))^(~p),(~x))),
         sub = :(∫((u)*((c)*((d)*((a) + (b)* (x))^(n))^(q))^(p),(x))),
        len = 1),
        (pat = :(∫((~!u)*((~!c)*((~!d)*((~!a) + (~!b)* (~x))^(~n))^(~q))^(~p),(~x))),
         sub = :(∫(    (    ((d)*((a) + (b)* (x))^(n))^(q))^(p),(x))),
        len = 1),
        (pat = :(∫((~!u)*((~!c)*((~!d)*((~!a) + (~!b)* (~x))^(~n))^(~q))^(~p),(~x))),
         sub = :(∫(    (    ((d)*((a) +      (x))^(n))^(q))^(p),(x))),
         len = 1),
        (pat = :(∫(~(!a) + ~(!b) * ~x, ~x)),
         sub = sub = :(∫((a + x),x)),
         len = 1),
        (pat = :(∫((~!u)*((~!e)*((~!a) + (~!b)*(~x)^(~!n))*((~c) + (~!d)*(~x)^(~!n)))^(~p),(~x))),
         sub = :(∫((u)*((e)*((a) + (b)*(x)^(n))*((c) + (d)*(x)^(n)))^(p),(x))),
         len = 2)
    ]

    for (i,(;pat, sub, len)) ∈ enumerate(ts)
        σs = _eachmatch(pat, sub)
        u = collect(σs)
        @test length(u) == len
    end
end


@testset "match" begin
    # match 1
    pat = :((~x)^(~x))
    sub = :((x+p)^(x+p))
    σ = _match(pat, sub)
    @test σ[:x] == :(p + x) # commutative arguments in standard order

    # _match 2 wildcards
    pat = :((~x)*sin((~y)))
    sub = :(x*sin(x))
    σ = _match(pat, sub)
    @test σ[:y] == :x && σ[:x] == :x && length(σ) == 2

    # _match can have more than 1 substitution
    pat = :(f((~~x),(~~y)))
    sub = :(f(a,b,c))
    σ = _match(pat, sub)
    @test Set(vcat(collect.(values(σ))...)) == Set([:a,:b,:c])

    # empty _match returns `nothing`
    pat = :(sin(~x))
    sub = :(sin(x)^2)
    @test isnothing(_match(pat, sub))

end

@testset "guards" begin
    ts = [
        (pat = :(~a*~x::(>=(0))),
         sub = :(2x),
         len=1),

        (pat = :(~x::(iseven)),
         sub = 2,
         len = 1),

        (pat = :(~x::(iseven)),
         sub = 3,
         len = 0),

        (pat = :(+(~~x::(u->iseven(length(u))))),
         sub = :(a + b + c),
         len = 0),
        (pat = :(+(~~x::(u->iseven(length(u))))),
         sub = :(a + b),
         len = 1),

    ]

    for (pat, sub, len) ∈ ts
        σs = AssociativeCommutativePatternMatching._eachmatch(pat, sub)
        @test length(collect(σs)) == len
    end

end

@testset "_rewrite" begin
    σ = AssociativeCommutativePatternMatching.match_dict(:x=>:x, :y=>1, :z=>[1,2,3], :w => [1,:(x^2)])

    @test AssociativeCommutativePatternMatching._rewrite(Expr, σ, :(sin(~x))) == :(sin(x))
    @test AssociativeCommutativePatternMatching._rewrite(Expr, σ, :(~y + ~x)) == :(1 + x)
    @test AssociativeCommutativePatternMatching._rewrite(Expr, σ, :(~x * cos((~x)^2))) == :(x*cos(x^2))

    # splatting is handled in a kludgy manner
    @test eval(AssociativeCommutativePatternMatching._rewrite(Expr, σ, :(+(~~z...)))) == 6
    @test eval(AssociativeCommutativePatternMatching._rewrite(Expr, σ, :(splat(+)(~~z)))) == 6

    # that works, but this fails --- the substitution is an expression...
    ex = :(log(1 + x^2))
    σ = AssociativeCommutativePatternMatching._match(:(log(1+(~~~w))), ex)
    x = exp(1) - 1
    @test_broken eval(_rewrite(Expr, σ, :(log1p(+(~~~w...))))) ≈ 1.0

end


@testset "_replace" begin

    # replace parts
    ex = :(log(1 + x^2) + log(1 + x^3))
    rule = :(log(1+(~x))) => :(log1p(~x))
    u = _replace(ex, rule)
    @test u == :(log1p(x^2) + log1p(x^3))
    @test_broken _replace(ex, :(log(1+(~~~x))) => :(log1p(+(~~~x...)))) == :(log1p(x ^ 2) + log1p(x ^ 3))

    ex = :(log(sin(x)) + tan(sin(x^2)))
    rule = sin => cos
    @test _replace(ex, rule) == :(log(cos(x)) + tan(cos(x ^ 2)))

    rule = :(sin(~x))=> :(tan(~x))
    @test _replace(ex, rule) == :(log(tan(x)) + tan(tan(x^2)))

    rule = :(sin(~x)) => :(tan((~x)/2))
    @test _replace(ex, rule) == :(log(tan(x/2)) + tan(tan(x^2/2)))

    rule = :(sin(~x)) => :(~x)
    @test _replace(ex, rule) == :(log(x) + tan(x^2))

    ex = :((1 + x^2)^2) # postwalk sees inner x^2 first and replaces, so rule applies twice
    rule = :((~x)^2) => :((~x)^4)
    @test _replace(ex, rule) == :((1 + (x ^ 4)) ^ 4)


    ex = :(sin(x + x*log(x) + cos(p + x + p + x^2)))
    rule = :(cos(x + (~~x))) => :(x__)
    @test _replace(ex, rule) == :(sin(x + x * log(x) + x__))

    @test _replace(:x, :p=>2) == :x
    @test _replace(:(1 + x^2), :(x^2) => 2) == :(1 + 2)  # 1 + 2 evaluates to 3
    # (~x) matches different parts of expression tree in _replace
    ex = :(sin(cos(a))*cos(b))
    rule = :(cos((~x))) => :(tan((~x)))
    @test _replace(ex, rule) == :(sin(tan(a)) * tan(b))

    # no variable in substitution
    @test _replace(:(sin(a)), :(sin((~x))) => :x) == :x
    @test _replace(:(sin(a)), :(sin((~x))) => :(~x)) == :a
    @test _replace(:(sin(a)), :(sin((~x))) => 2) == 2
end

@testset "_replace head" begin
    # replace operation
    ex = :(log(1 + x^2) + log(1 + x^3))
    rule = log=>log1p
    @test _replace(ex, rule) == :(log1p(1 + x ^ 2) + log1p(1 + x ^ 3))

    ex = :(f(a,a,b))
    rule = :(f(~~x)) => :(g(~~x))
    u = _replace(ex, rule)
    @test operation(u) == :g # :(g(Any[:a, :a, :b]))
end

@testset "_replace exact" begin
    # no wild card
    ex = :(x^2 + x^4)
    @test _replace(ex, :(x^2) => :x) == :(x + x^4)

    ex = :(x * sin(x))
    @test _replace(ex, :(x*sin(x)) => :x) == :x
end

@testset "simplify" begin
    si(ex) = AssociativeCommutativePatternMatching._simplify(ex, Expr)

    ss = (:(2x + 3x + 4),
          :(sin(x)/cos(x)),
          :(20*sin(x) * cos(x)),
          :(10*sin(x^2)^2 + 10*cos(x^2)^2 + 10),
          :(10*log(x)),
          )

    for ex ∈ ss
        @test ex != si(ex)
    end
end
