## ---- note -----
#=

This code is derived from, rule2.jl at https://github.com/JuliaSymbolics/SymbolicIntegration.jl/blob/main/src/methods/rule_based/rule2.jl

There are some modifications for commutivity following ideas from Krebber, which are also implemented in AssociativeCommutativePatternMatching.jl.

Using Krebber's language we have

* substitution (match) is σ a map between pattern terms and subject terms such that a substitution of the pattern terms returns the subject (σ(t) = s). This uses an ImmutableDict{Symbol, Any} to store a match or a partial match

* An empty substitution is partial match and a possible match, when there are not wild cards

* A sentinel is used to indicate *no possible substitution* and is here a FAIL_DICT

* A set of matches (`θ` or `σs`) allows for different matches due to commutivity/associativity. This set is empty if there are no matches. We use a vector to store this: MatchDict[MatchDict()] is an initial set with a initial partial match specified.


A pattern to match against has wildcards. We have:

* ~x: match one argument (a slot variable)
* ~!x: match one argument, possibly through a default (a defslot)
* ~~x: match 0, 1, or more arguments (returns a tuple); A segment (star) variable (`is_segment`)
* ~~~x: match 1 or more arguments (returns a tuple); A plus variable (`is_plus`)

A pattern can only have one wildcard of a given name (no ~x + ~~x, say).

# test cases -- AssociativeCommutativePatternMatching uses associativity in its considerations (2,4). Both enumerate every way of sharing the arguments among several segments (6, 7): under a commutative operation any sub-multiset, under another operation contiguous runs. The Rule1 (from SymbolicIntegration) doesn't do segments right (in my mind)

                                      # ACPM  | Rule2 | Rule1 (match only)
1. eachmatch(:(~x), a + b + c)        # 1 | 1 | yes
2. eachmatch(:(~x + ~y), a + b + c)   # 6 | 0 | no (not associative matching!)
3. eachmatch(:(~x + ~!y), a + b + c)  # 6 | 1 | yes
4. eachmatch(:(~x + ~~y), a+b+c)      # 7⁺| 4 | no # ⁺ ~x accts like ~~~x
5. eachmatch(:(~x + ~~~y), a+b+c)     # 6 | 3 | not
6. eachmatch(:(~~x + ~~y), a+b+c)     # 8 | 8 | no
7. eachmatch(:(~~~x + ~~~y), a+b+c)   # 6 | 6 | no

=#

## ----- rule2.jl -------

# This is derived from https://github.com/JuliaSymbolics/SymbolicIntegration.jl/tree/main/src/methods/rule_based/rule2.jl
# Licensed under MIT with Copyright (c) 2022 Harald Hofstätter, Mattia Micheletta Merlin, Chris Rackauckas, and other contributors


# TODO ~a*(~b*~c) currently will not match a*b*c . a fix is possible

# for when the rule contains a symbol, like ℯ, or a literal number
function check_expr_r(@nospecialize(data), rule::Real, σs::𝑀, once::Bool=false)::𝑀
    eq_expr(rule, data) && return σs
    return NO_MATCH
end

function check_expr_r(@nospecialize(data), rule::Symbol, σs::𝑀, once::Bool=false)::𝑀
    eq_expr(data, rule) && return σs
    return NO_MATCH
end

# main function
# With `once`, only the first match is needed: a search may stop at its first
# match when nothing after it can reject that match, so `once` is passed on
# only to the last step of a search (the last argument, the last pattern of a
# commutative operation, ...). The first match is that of the full search.
check_expr_r(data, rule; once::Bool=false)::𝑀 =
    check_expr_r(data, rule, [MatchDict()], once)

function check_expr_r(@nospecialize(data), rule::Expr, σs::𝑀, once::Bool=false)::𝑀
    # @show :cer, data, rule
    if !iscall(rule)
        #@show :what_is, rule
    end

    opᵣ = operation(rule)

    if is_𝑋(opᵣ)
        # @show :is_𝑋, data, rule
        # peel off hope for single argument!
        !iscall(data) && return MatchDict[] # XXX <---

        value = iscall(data) ? operation(data) : identity
        σ′ = match_dict(varname(opᵣ) => value)
        σs = merge_vectors_of_matches(σs, σ′)
        arg_data, arg_rule = arguments(data), arguments(rule)
        if length(arg_data) > 1
            if iscommutative(opᵣ)
                return check_commutative(arg_data, arg_rule, σs, once)
            else
                return ceoaa(arg_data, arg_rule, σs, once)
            end
        else
            data, rule = (isempty(arg_data) ? arg_data : only(arg_data)), only(arg_rule)
        end
    end

    # rule is a single variable
    if is_𝑋(rule)
        return just_variable(data, rule, σs, once)
    end

    # if there is a deflsot in the arguments
    i = findfirst(is_defslot, arguments(rule))
    if i !== nothing
        return has_defslot(i, data, rule, σs, once)
    end

    # if there is a segment in the (only) argument
    if (iscall(rule) &&
        length(arguments(rule)) == 1 &&
#        is_segment(first(arguments(rule)))
        (is_segment(first(arguments(rule))) ||
         is_plus(first(arguments(rule))))
        )
        # @show :hi
        return only_argument_is_segment(data, rule, σs)
    end

    # rule is a normal call, check operation and arguments
    if (operation(rule) == ://) && _is_rational(data)
        return has_rational(data, rule, σs)
    end

    !iscall(data) && return NO_MATCH

    # check opᵣ for special cases where
    # powers are represented differently
    opᵣ, 𝑜𝑝ₛ = operation(rule), _opsym(operation(data))

    if opᵣ ∈ (:^, :sqrt, :exp) ||
        (opᵣ, 𝑜𝑝ₛ) ∈ ((:/,:^),
                      (:/,:*),
                      (:/,:/),
                      )

        return different_powers(data, rule, σs, once)
    end


    # gimmick to make Neim work in some cases:
    # * if data is a division transform it to a multiplication
    # (the final solution would be remove divisions form rules)
    # * if the rule is a product, at least one of the factors is a power, and data is a division
    neim_pass, arg_data, arg_rule = neim_rewrite(data, rule)
    𝑜𝑝ₛ != opᵣ && !neim_pass && return NO_MATCH

    # segments variables means number of arguments might not match
    if (any(is_segment, arg_rule))
        # @show :has_any
        return has_any_segment(𝑜𝑝ₛ, arg_data, opᵣ, arg_rule,  σs, once)
    end

    if (any(is_plus, arg_rule))
        # @show :has_plus, arg_data, arg_rule
        return has_any_plus(𝑜𝑝ₛ, arg_data, opᵣ, arg_rule,  σs, once)
    end


    (length(arg_data) != length(arg_rule)) && return MatchDict[]
    if iscommutative(opᵣ)
        σ′s = check_commutative(arg_data, arg_rule, σs, once)
        return isempty(σ′s) ? NO_MATCH : σ′s
    end
    # normal checks
    return ceoaa(arg_data, arg_rule, σs, once)
end

# check expression of all arguments
# elements of arg_rule can be Expr or Real
function ceoaa(@nospecialize(arg_data), arg_rule, σs::𝑀, once::Bool=false)::𝑀
    if all(is_𝑋, arg_rule) && !any(is_op, arg_rule)
        nseg = count(is_segment, arg_rule) # no segment? need same wild
        iszero(nseg) && count(is_slot, arg_rule) != length(arg_data) &&
            return NO_MATCH
    end
    σs == NO_MATCH && return NO_MATCH
    if (any(is_segment, arg_rule))
        return has_any_segment(nothing, arg_data, nothing, arg_rule,  σs, once)
    end
    if (any(is_plus, arg_rule))
        return has_any_plus(nothing, arg_data, nothing, arg_rule,  σs, once)
    end
    σ′s = σs
    n, i = min(length(arg_data), length(arg_rule)), 0
    for (a, b) in zip(arg_data, arg_rule)
        i += 1
        σ′s = check_expr_r(a, b, σ′s, once && i == n) # later arguments may reject a match
        σ′s == NO_MATCH && return NO_MATCH
    end
    return σ′s
end

# match a single variable
function just_variable(@nospecialize(data), rule, σs::𝑀, once::Bool=false)::𝑀
    #@show :jv, data, rule
    @assert is_𝑋(rule)
    var = varname(rule)
    val = (is_segment(rule) || is_plus(rule)) ? (data,) : data
    isempty(σs) && return NO_MATCH
    ms = MatchDict[]
    for σ ∈ σs
        if haskey(σ, var) # if the slot has already been matched
            σvar = σ[var]
            isequal(σvar, val) && push!(ms, σ)
        else
            # if never been matched
            if has_predicate(rule)
                pred = get_predicate(rule)
                !_evalguard(pred, val) && continue
            end
            push!(ms, match_dict(σ, var=> val))
        end
        once && !isempty(ms) && break
    end
    return isempty(ms) ? NO_MATCH : ms
end

# expression has defslot
function has_defslot(i, @nospecialize(data), rule, σs, once::Bool=false)
    # @show :has_defslot, data, rule
    op = operation(rule)
    if op ∈ (:^, :/)
        i == 1 && return MatchDict[]
    end
    ps = copy(arguments(rule))
    pᵢ = ps[i]
    qᵢ = :(~$(pᵢ.args[2].args[2]))
    ps[i] = qᵢ

    # build rule expr without defslot and check it
    newr = Expr(:call, operation(rule), ps...) # not pterm here!
    σ′s = check_expr_r(data, newr, σs, once)
    σ′s != MatchDict[] && return σ′s # had a match

    # if no normal match, check only the non-defslot part of the rule
    deleteat!(ps, i)
    tmp = pterm(operation(rule), ps)
    σs = check_expr_r(data, tmp, σs)
    σs == MatchDict[] && return MatchDict[]

    var = varname(qᵢ)
    value = get(defslot_op_map, operation(rule), -1)
    _merge_single_expr(σs, var, value)

end

function only_argument_is_segment(@nospecialize(data), rule, σs, op=nothing)
    # @show :only_argument_is_segment, data, rule
    !iscall(data) && return MatchDict[]
    opₛ, opᵣ = _opsym(operation(data)), operation(rule)
    opₛ == opᵣ || return MatchDict[]

    # a segment binds to the tuple of arguments, as in has_any_segment
    seg = only(arguments(rule))
    var = varname(seg)
    args = tuple(arguments(data)...)
    is_plus(seg) && isempty(args) && return MatchDict[]
    _segment_guard(seg, args) || return MatchDict[]
    _merge_single_expr(σs, var, args)
end

function has_rational(data, rule, σs)
    # @show :has_rational, data, rule
    # rational is a special case, in the integration rules is present only in between numbers, like 1//2
    as = arguments(rule)
    data = _unwrap_const(data)
    data.num == first(as) && data.den == last(as) && return σs
    # r.num == rule.args[2] && r.den == rule.args[3] && return matches::MatchDict
    return MatchDict[]
end


# make powers equivalent for checking
# e.g. sqrt(x) --> x^(1//2)
function different_powers(@nospecialize(data), rule, σs::𝑀, once::Bool=false)::𝑀
    # @show :different_powers, data, rule
    opᵣ, opₛ = operation(rule), _opsym(operation(data))
    arg_data = arguments(data)
    arg_rule = arguments(rule)
    b = first(arg_data)

    if opᵣ === :^
        # try first normal checks
        if (opₛ === :^)
            σ′s = ceoaa(arg_data, arg_rule, σs, once)
            !isempty(σ′s) && return σ′s
        end

        # try building frankestein arg_data (fad)
        fad = Vector{Any}(undef, 2)
        is1divsmth = (opₛ == :/) && isequal(1, _unwrap_const(first(arg_data)))
        if is1divsmth && _is_operation(^)(arg_data[2]) #iscall(arg_data[2]) && (Symbol(operation(arg_data[2])) == :^)

            # if data is of the alternative form 1/(...)^(...)
            m = arg_data[2]
            fad[1] = arguments(m)[1]
            fad[2] = -1*arguments(m)[2]

        elseif is1divsmth && _is_operation(sqrt)(arg_data[2]) #iscall(arg_data[2]) && (Symbol(operation(arg_data[2])) == :sqrt)
            # if data is of the alternative form 1/sqrt(...),
            # it might match with exponent -1//2
            m = arg_data[2] # like b^m
            fad[1] = arguments(m)[1]
            fad[2] = -1//2

        elseif is1divsmth && _is_operation(exp)(arg_data[2]) #iscall(arg_data[2]) &&
            #(Symbol(operation(arg_data[2])) === :exp)
            # if data is of the alternative form 1/exp(...),
            # it might match ℯ ^ -...
            m = arg_data[2] # like b^m
            pow = first(arguments(m))

            fad[1] = ℯ
            fad[2] = sterm(-, (pow,))

        elseif is1divsmth
            # if data is of the alternative form 1/(...),
            # it might match with exponent = -1
            m = arg_data[2] # like b^m
            fad[1] = m
            fad[2] = -1
        elseif (opₛ  === :^) && iscall(b) &&
            (_opsym(operation(b)) === :/) &&
            _isone(arguments(b)[1])

            # if data is of the alternative form (1/...)^(...)
            m = arg_data[2] # like b^m
            fad[1] = arguments(b)[2]
            fad[2] = -1*m

        elseif opₛ === :exp

            # if data is a exp call, it might match with base e
            fad[1] = ℯ
            fad[2] = b

        elseif opₛ === :sqrt
            # if data is a sqrt call, it might match with exponent 1//2
            fad[1] = b
            fad[2] = 1//2
#        elseif opₛ === :/
#            # rule is ^ we have /, turn into ^-1
#            #push!(fad, arguments(m)[1], -1*arguments(m)[2])
        else
            return MatchDict[]

        end
        return ceoaa(fad, arg_rule, σs, once)

    elseif opᵣ === :sqrt
        if (opₛ === :sqrt)
            tocheck = arg_data # normal checks
        # `isequal`, not `∈`: `==` need not return a Bool for a symbolic exponent
        elseif (opₛ === :^) && any(isequal(_unwrap_const(arg_data[2])), (1//2, :(1//2)))
            tocheck = (b,)
        else
            return MatchDict[]
        end

        return ceoaa(tocheck, arg_rule, σs, once)

    elseif opᵣ === :exp
        if (opₛ === :exp)
            tocheck = arg_data # normal checks
        elseif (opₛ === :^) && (_unwrap_const(b) ∈ (ℯ,:ℯ))
            m = arg_data[2]
            tocheck = (m,)
        else
            return MatchDict[]
        end

        return ceoaa(tocheck, arg_rule, σs, once)
    elseif (opᵣ, opₛ) == (:/, :*)
        # rule is / but may be canonicalized to
        # turn rule into ^-1 terms and check commutatively
        return check_commutative(arg_data, _rule_as_powers(rule), σs, once)

    elseif (opᵣ, opₛ) == (:/, :/)
        # the matches numerator to numerator and denominator to denominator,
        # and those comparing both as products of powers: e.g. the rule
        # `(~u)^(~p) / ~x` and the subject `1 / (x * log(x))`, as
        # `[(~u)^(~p), (~x)^-1]` and `[x^-1, log(x)^-1]`. Both are kept, as a
        # match of one kind may conflict with the rest of the pattern.
        σ′s = ceoaa(arg_data, arg_rule, σs, once)
        once && !isempty(σ′s) && return σ′s
        σ″s = check_commutative(_data_as_powers(data), _rule_as_powers(rule), σs, once)
        return unique!(vcat(σ′s, σ″s))

    elseif (opᵣ, opₛ) == (:/, :^)
        # :(1/~x^~n) ~ x^(-n)
        # rewrite rule as a * b^(-1)
        a, b = arguments(rule)
        if is_operation(:^)(b) # combine exponents
            u, v = arguments(b)
            if is_operation(:(//))(v)
                n,d = arguments(v)
                v′ = pterm(:(//), (-n, d))
            elseif !isa(u, Integer) && isa(v, Number)
                v′ = -v
            else
                v′ = pterm(:*, (v, -1.0))
            end

            b′ = pterm(:^, (u, v′))
        elseif is_operation(:sqrt)(b) # 1/sqrt(u) is u^(-1//2)
            # the exponent as a value: it compares equal to a symbolic -1/2
            b′ = pterm(:^, (only(arguments(b)), -1//2))
        else
            b′ = Expr(:call, :^, b, -1)
        end
        # multiply by a once
        rule′ = (isa(a, Number) && isone(a)) ? b′ : Expr(:call, :*, a, b′)
        return check_expr_r(data, rule′, σs, once)

    #end
    elseif (opᵣ, opₛ) == (:*, :/)
        u, v = arg_data
        v′ = sterm(^, [v, -1])
        return check_commutative((u, v′), arg_rule,  σs, once)
    end
    return NO_MATCH
end

function neim_rewrite(@nospecialize(data), rule)
    neim_pass = false
    arg_rule, arg_data = arguments(rule), arguments(data)
    opᵣ, opₛ = operation(rule), _opsym(operation(data))
    if (opᵣ === :*) && opₛ === :/ && any(is_operation(:^), arg_rule)

        neim_pass = true

        # the numerator's factors, then each factor of the denominator with a
        # negative power. (The denominator was tested with the data's own
        # operation, always `/` here, so a product denominator was inverted
        # as a whole, giving too few factors.)
        arg_data = _data_as_powers(data)

        # printdb(4,"Applying neim trick, new arg_data is $arg_data")
    end
    return (neim_pass, arg_data, arg_rule)

end

# A guard on a segment (`~~x::pred`) is passed the tuple of matched values.
_segment_guard(segpat, vals::Tuple) =
    !has_predicate(segpat) || _evalguard(get_predicate(segpat), vals)

# `once`: stop at the first match, as `_cmatch` does
function has_any_segment(𝑜𝑝ₛ, @nospecialize(arg_data),
                         opᵣ, arg_rule, σs, once::Bool=false)
    # @show :has_any_segment, arg_data, arg_rule
    σs == NO_MATCH && return NO_MATCH
    seg, notseg, seg_positions = _split_segments(arg_rule)
    # @show seg, notseg, seg_positions
    n,m = length(arg_data), length(notseg)
    m > n && return MatchDict[]
    if m == 0 && length(seg) == 1
        # fast path for the overwhelmingly common single-segment case:
        # the segment takes every argument
        v = first(seg)
        is_plus(v) && isempty(arg_data) && return MatchDict[]
        var = varname(v)
        vals = tuple(arg_data...)
        _segment_guard(v, vals) || return MatchDict[]
        σ′s = MatchDict[]
        for σ ∈ σs
            if haskey(σ, var)
                isequal(vals, σ[var]) && push!(σ′s, σ)
            else
                push!(σ′s, match_dict(σ, var => vals))
            end
        end
        return σ′s
    end

    # an ordered operation: segments take contiguous runs of the arguments
    iscommutative(opᵣ) || return _ordered_segments(arg_data, arg_rule, seg_positions, σs, once)

    # a commutative operation: the arguments not matched by the other
    # patterns are shared among the segments in every possible way
    seg_varnames = varname.(seg)
    seg_is_plus = is_plus.(seg)
    σ′′s = MatchDict[]
    if m == 0
        _distribute_segments!(σ′′s, seg, seg_varnames, seg_is_plus, tuple(arg_data...), σs, once)
        return σ′′s
    end
    # these only depend on opᵣ/notseg/seg, not on the subset `ind`
    # chosen below, so compute them once rather than once per
    # combination (there are C(n,m) combinations, which can be
    # large)
    pat′ = pterm(opᵣ, notseg) # can be an issue!
    for ind ∈ combinations(1:n, m)
        # take m of the values and match
        sub′ = sterm(𝑜𝑝ₛ, arg_data[ind])
        # the values left for the segments
        val = length(ind) < n ?
            _tuple_without_indices(arg_data, ind, n) :
            ()
        count(seg_is_plus) > length(val) && continue
        for σ ∈ σs
            σ′s = check_expr_r(sub′, pat′, [σ])
            σ′s == NO_MATCH && continue
            _distribute_segments!(σ′′s, seg, seg_varnames, seg_is_plus, val, σ′s, once)
            once && !isempty(σ′′s) && return σ′′s
        end
    end
    # match all segments with (), then match the rest
    σ′′′ = match_dict()
    for v ∈ seg
        if is_plus(v) || !_segment_guard(v, ())
            σ′′′ = FAIL_DICT
            break
        else
            σ′′′ = match_dict(σ′′′, varname(v) => ())
        end
    end
    σ′′′s = merge_vectors_of_matches(σs, σ′′′)
    sub′ = sterm(𝑜𝑝ₛ, arg_data)
    σ′′′s = check_expr_r(sub′, pat′, σ′′′s)
    σ′′′s != NO_MATCH && (length(seg) == 1 ? append!(σ′′s, σ′′′s) : _append_unique!(σ′′s, σ′′′s))

    return isempty(σ′′s) ? NO_MATCH : σ′′s
end

# Segments of an ordered operation take contiguous runs of the arguments.
# match ~a,~~b,~c,~~d against say l,m,n,o,p,q
# has l|()|m|(nopq) # n - nontsegs + 1 choices for first
#     l|(m)|n|(opq) # then ,,, + 1 for second (if more)
#     l|(mn)|o|(pq) # then ... + 1 for third (if more)
#     l|(mno)|p|(q)
#     l|(mnop)|q|()
function _ordered_segments(@nospecialize(arg_data), arg_rule, seg_positions, σs, once::Bool=false)
    nsegs = length(seg_positions)
    k = length(arg_rule) - nsegs
    n = length(arg_data) - k

    σ′′s =  MatchDict[]
    for α ∈ _compositions(n, nsegs)
        σ′s = σs
        j = 1 # index in data_rule
        l = 1 # index in itr,
        nomatch = false
        for (i,pat) ∈ enumerate(arg_rule)
            nomatch && continue
            if l > nsegs || i != seg_positions[l]
                σ′s = check_expr_r(arg_data[j], pat, σ′s)
                σ′s == NO_MATCH && (nomatch = true)
                j = j + 1
            else
                a = α[l]
                l = l + 1
                # `~~~`-style (is_plus, "one or more") segments can
                # never be validly bound to an empty selection
                if a == 0 && is_plus(pat)
                    nomatch = true
                    continue
                end
                var = varname(pat)
                value = tuple(arg_data[j:(j+a-1)]...)
                if !_segment_guard(pat, value)
                    nomatch = true
                    continue
                end
                σ′ = match_dict(var => value)
                σ′s = _merge_single(σ′s, σ′)
                σ′s == NO_MATCH && (nomatch = true)
                j = j + a
            end
        end
        σ′s == NO_MATCH && continue
        !nomatch && append!(σ′′s, σ′s)
        once && !isempty(σ′′s) && break
    end
    return isempty(σ′′s) ? NO_MATCH : σ′′s
end

# Every way to share the values `vals` among the segment patterns `seg` of a
# commutative operation: each value goes to one segment (`who[j]` is the
# segment of the jth value), a segment keeps its values in their order, a
# `~~~` segment needs at least one, and a segment already bound must get the
# same values. The matches extending each of `σs` are appended to `out`. For k
# segments and r values there are k^r ways; r is small in practice. Equal
# values give the same match in several ways, so then each is kept once. With
# `once`, stop at the first match.
function _distribute_segments!(out, seg, seg_varnames, seg_is_plus, @nospecialize(vals), σs, once::Bool=false)
    k, r = length(seg), length(vals)
    count(seg_is_plus) > r && return out
    if k == 1 # one segment takes every value
        _extend_segments!(out, seg, seg_varnames, (vals,), σs, false, once)
        return out
    end
    dedupe = !once && _has_equal_values(vals) # the first match needs no check
    parts = [Any[] for _ ∈ 1:k]
    tups = Vector{Any}(undef, k)
    who = ones(Int, r)
    while true
        ok = true
        for i ∈ 1:k
            seg_is_plus[i] || continue
            any(==(i), who) || (ok = false; break)
        end
        if ok
            foreach(empty!, parts)
            for j ∈ 1:r
                push!(parts[who[j]], vals[j])
            end
            for i ∈ 1:k
                tups[i] = Tuple(parts[i])
            end
            _extend_segments!(out, seg, seg_varnames, tups, σs, dedupe, once)
            once && !isempty(out) && return out
        end
        # the next assignment, counting in base k
        j = 1
        while j ≤ r && who[j] == k
            who[j] = 1
            j += 1
        end
        j > r && break
        who[j] += 1
    end
    return out
end

# bind segment i to assignment[i] in each of σs, if they agree; append to `out`
function _extend_segments!(out, seg, seg_varnames, assignment, σs, dedupe::Bool, once::Bool)
    for σ ∈ σs
        τ = σ
        good = true
        for i ∈ eachindex(seg)
            a = assignment[i]
            var = seg_varnames[i]
            if haskey(τ, var)
                isequal(a, τ[var]) || (good = false; break)
            else
                _segment_guard(seg[i], a) || (good = false; break)
                τ = match_dict(τ, var => a)
            end
        end
        good || continue
        dedupe && any(t -> _isequal_match(t, τ), out) && continue
        push!(out, τ)
        once && return out
    end
    return out
end

function _has_equal_values(@nospecialize(vals))
    for i ∈ eachindex(vals), j ∈ 1:(i - 1)
        _cheap_isequal(vals[i], vals[j]) && return true
    end
    return false
end


function has_any_plus(𝑜𝑝ₛ, @nospecialize(arg_data),
                      opᵣ, arg_rule, σs, once::Bool=false)
    # @show :has_any_plus, arg_data, arg_rule
    has_any_segment(𝑜𝑝ₛ, arg_data,
                      opᵣ, arg_rule, σs, once)
end
@inline function _commutative_priority(pat)
    is_defslot(pat) && return 3
    has_predicate(pat) && return 2
    is_slot(pat) && return 4
    has_𝑋(pat) && return 1
    return 0
end

function _append_unique!(out, σs)
    for σ ∈ σs
        any(τ -> _isequal_match(τ, σ), out) || push!(out, σ)
    end
    return out
end

# cheap, allocation-avoiding equality check used only to detect/prune
# duplicate-valued arguments below. Falls back to `isequal` only when the
# concrete types already match, since comparing mismatched concrete types
# (e.g. a literal `1` against a symbolic expression) can otherwise fall
# through to generic, allocating promotion machinery for what can never be
# a duplicate for pruning purposes.
@inline _cheap_isequal(a, b) = a === b || (typeof(a) === typeof(b) && isequal(a, b))

function _check_commutative!(out, used, @nospecialize(arg_data), arg_rule, order, k, σs::𝑀, once::Bool=false)::𝑀
    # @show :check_commutative
    σs == NO_MATCH && return out
    k > length(order) && return _append_unique!(out, σs)

    pat = arg_rule[order[k]]
    for j ∈ eachindex(arg_data)
        used[j] && continue
        val = arg_data[j]

        # When several unused data elements are equal (a common case:
        # repeated terms like x + x + y), trying each of them for the
        # *current* pattern slot explores symmetric branches whose eventual
        # results are identical (matching only depends on the *value*,
        # never on which physical index produced it, and the multiset of
        # values left over for the remaining patterns is the same no matter
        # which equal-valued index is consumed now). So only the first
        # unused occurrence of each distinct value needs to be tried at
        # this level. Detect "already tried at this level" by scanning
        # backwards for an earlier still-unused index with an equal value;
        # this needs no extra allocation (arg_data/used are already
        # available) and is cheap since argument lists are small.
        isdup = false
        for jj ∈ 1:(j - 1)
            if !used[jj] && _cheap_isequal(arg_data[jj], val)
                isdup = true
                break
            end
        end
        isdup && continue

        σ′s = check_expr_r(val, pat, σs, once && k == length(order)) # later patterns may reject a match
        σ′s == NO_MATCH && continue
        used[j] = true
        _check_commutative!(out, used, arg_data, arg_rule, order, k + 1, σ′s, once)
        used[j] = false
        once && !isempty(out) && break
    end
    return out
end

function check_commutative(@nospecialize(arg_data), arg_rule, σs::𝑀, once::Bool=false)::𝑀
    # commutative checks
    length(arg_data) != length(arg_rule) && return NO_MATCH

    order = sortperm(collect(eachindex(arg_rule)); by = i -> _commutative_priority(arg_rule[i]))
    used = falses(length(arg_data))
    σ′′s = MatchDict[]
    _check_commutative!(σ′′s, used, arg_data, arg_rule, order, 1, σs, once)
    return isempty(σ′′s) ? NO_MATCH : σ′′s
end
