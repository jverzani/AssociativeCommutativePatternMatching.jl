# The patterns and subjects compared, as (group, pattern, subject, note).
# Subjects are built as SymbolicUtils terms from the variables x y z a b c t,
# so what is matched is the term as SymbolicUtils stores it (a + a is 2a, say).
# Guards use functions from Base, which every matcher can find.
[
    # ---- plain slots, literals and repeated slots
    ("basics", :(~x), :(sin(x)), "a slot matches anything"),
    ("basics", :(sin(~x)), :(sin(x + 1)), ""),
    ("basics", :((~x)^2), :((x + a)^2), "a literal exponent"),
    ("basics", :((~x)^(~x)), :((x + a)^(x + a)), "a repeated slot"),
    ("basics", :((~x)^(~x)), :((x + a)^(x + b)), "a repeated slot, different values: no match"),
    ("basics", :(sin(~x) * cos(~x)), :(sin(t) * cos(t)), "a repeated slot across factors"),
    ("basics", :(~x + ~x), :(a + a), "SymbolicUtils stores a + a as 2a"),
    ("basics", :(log(~x)), :(log(2x)), ""),

    # ---- commutativity
    ("commutative", :(~x + ~y), :(a + b), "two ways"),
    ("commutative", :(~x * ~y), :(a * b), "two ways"),
    ("commutative", :(~x + ~y + ~z), :(a + b + c), "3! ways"),
    ("commutative", :(sin(~x) + ~y), :(sin(a) + b), "one way"),
    ("commutative", :(~x * sin(~x)), :(x * sin(x)), "a repeated slot in a product"),
    ("commutative", :(~a * ~x + ~b), :(2x + 3), ""),
    ("commutative", :((~x)^2 + (~y)^2), :(a^2 + b^2), ""),
    ("commutative", :(sin(~x)^2 + cos(~x)^2), :(sin(t)^2 + cos(t)^2), ""),
    ("commutative", :(sin(~x) + cos(~y)), :(cos(a) + sin(b)), "the subject in the other order"),

    # ---- associativity: a slot takes several terms
    ("associative", :(~x + ~y), :(a + b + c), "three terms, two slots"),
    ("associative", :(~x * ~y), :(a * b * c), "three factors, two slots"),
    ("associative", :(~x + sin(~y)), :(a + b + sin(c)), ""),
    ("associative", :(~x * (~y)^2), :(a * b * c^2), ""),
    ("associative", :(~x + ~y), :(a + b + c + t), "four terms, two slots"),

    # ---- segments
    ("segments", :(+(~~x)), :(a + b + c), "the arguments of a sum"),
    ("segments", :(~x + ~~y), :(a + b + c), ""),
    ("segments", :(~~x + ~~y), :(a + b + c), "two segments"),
    ("segments", :(sin(~x) + ~~y), :(sin(a) + b + c), ""),
    ("segments", :(~~x * sin(~y)), :(a * b * sin(c)), ""),
    ("segments", :(~x + ~~~y), :(a + b), "~~~y needs at least one term"),
    ("segments", :(~x + ~~~y), :(a), "~~~y needs at least one term: no match"),

    # ---- default values
    ("defaults", :(~!a * ~x), :(3x), ""),
    ("defaults", :(~!a * ~x), :(x), "a = 1"),
    ("defaults", :(~!a + ~x), :(x + 2), ""),
    ("defaults", :(~!a + ~x), :(x), "a = 0"),
    ("defaults", :((~x)^(~!m)), :(x^3), ""),
    ("defaults", :((~x)^(~!m)), :(x), "m = 1"),
    ("defaults", :(~!a * (~x)^(~!m)), :(5 * x^2), ""),
    ("defaults", :(~!a + ~!b * ~x), :(x), "a = 0, b = 1"),

    # ---- guards
    ("guards", :((~x)^(~n::iseven)), :(x^2), ""),
    ("guards", :((~x)^(~n::iseven)), :(x^3), "fails the guard"),
    ("guards", :(~a::isinteger * ~x), :(3x), ""),
    ("guards", :((~x)^(~n::isodd) + ~y), :(x^3 + a), ""),

    # ---- powers written differently
    ("powers", :((~u)^(~m)), :(1 / x), ""),
    ("powers", :((~u)^(~m)), :(1 / x^2), ""),
    ("powers", :((~u)^(~m)), :(sqrt(x)), ""),
    ("powers", :((~u)^(~m)), :(1 / sqrt(x)), ""),
    ("powers", :((~u)^(~m)), :(exp(x)), ""),
    ("powers", :(sqrt(~u)), :(x^(1//2)), ""),
    ("powers", :(exp(~u)), :(ℯ^x), ""),
    ("powers", :(1 / ~u), :(x^(-1)), ""),
    ("powers", :((~u)^(~m) * ~v), :(a / b), "a quotient as a product"),
    ("powers", :((~u)^(~m) * (~v)^(~n)), :(a^2 / b^3), ""),

    # ---- nested, integration-rule like
    ("nested", :(sin(~x + ~y)), :(sin(a + b)), ""),
    ("nested", :((~a + ~b * ~x)^(~m)), :((2 + 3x)^5), ""),
    ("nested", :((~!a + ~!b * ~x)^(~!m)), :((1 + x)^4), "b = 1"),
    ("nested", :((~a + ~b * ~x)^(~m) * (~c + ~d * ~x)^(~n)), :((1 + 2x)^3 * (4 + 5x)^6), ""),
    ("nested", :(~x * (~!a + ~!b * ~x)^(~!m)), :(x * (2 + 3x)^4), "a repeated slot inside and outside"),

    # ---- an operation as a slot
    ("operation", :((~F)(~x)), :(sin(a)), ""),
    ("operation", :((~F)(~x)^2), :(cos(x)^2), ""),

    # ---- no match expected
    ("no match", :(sin(~x)), :(cos(x)), ""),
    ("no match", :(~x + ~x), :(a + b), ""),
    ("no match", :((~x)^2), :(x^3), ""),
    ("no match", :(~x * ~y), :(a + b), ""),
]
