#=
Implement algorithm, through Ch. 3, of of matchpy paper:

Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables by Manuel Krebber

We use expressions to indicate patterns with wildcards specified as:

* `~x`, `~x::pred`     --- slot variable, 1 argument (save associativity)
* `~!x`                --- default slot
* `~~x`, `~~x::pred`   --- 0, 1, or more matches, match holds a container
* `~~~x`, `~~~x::pred` --- 1 or more matches, , match holds a container

Where:
* all wildcard variables need unique `varname`s (no ~x and ~~x in same pattern)

Notation of paper:
𝐹 function heads
Symbolic objects split into
𝐹₀ 0-arity expressions
𝐿 all symbolic variables
𝑋 wildcard expressions which split into -- is_𝑋
Xʳᵉᵍᵘˡᵃʳ, regular
Xᵖˡᵘˢ, plus variables
Xˢᵗᵃʳ, star variables

t matches s if there is a substitution with σ(t) = s
=#


# θ [\theta]  is an iterable of substitutions;
# returns an iterable of substitutions, possibly empty
function match_one_to_one(ss, p, fₐ = nothing, θ = (match_dict(),))
    #@show :m11, ss, p, fₐ
    n = length(ss)
    if !has_𝑋(p)              # constant expression/symbol/number
        # match if p == ss[1]
        n == 1 && eq_expr(only(ss), p) && return θ
        return ∅

    elseif is_slot_or_defslot(p) && isnothing(fₐ)  # regular variable
        if n == 1
            s₁ = only(ss)
            pass_any_guard(p, s₁) || return ∅

            var = varname(p)
            σ′ = match_dict(var => s₁)
            return union_merge(θ, σ′)
        end

    elseif iscall(p) && any(has_defslot, arguments(p))
        return clear_defslots(ss, p, fₐ, θ)

    elseif is_𝑋(p)            # sequence variable?
        var = varname(p)
        value = is_slot_or_defslot(p) && !isnothing(fₐ) ? sterm(fₐ, ss) : ss
        pass_any_guard(p, value) || return ∅
        σ′ = match_dict(var => value)

        if is_segment(p) || n ≥ 1
            return union_merge(θ, σ′)
        end

    elseif n == 1
        s = only(ss)
        iscall(s) || return ∅ # p is non constant, s must be a call

        p = normalize_pattern(p,s)
        opₛ, ss = normalize_subject(s, p)
        opₚ = operation(p)
        if is_𝑋(opₚ) # check for variable function head
            σ′ = match_dict(varname(opₚ) => opₛ)
            θ = union_merge(θ, σ′)
        else
            _opsym(opₛ) == opₚ || return ∅ # can't have defslot in p at this level
        end
        ps = arguments(p)
        fₐ′ = isassociative(opₛ) ? opₛ : nothing
        λ = iscommutative(opₛ) ? match_commutative_sequence : match_sequence
        return λ(ss, ps, fₐ′, θ)
    end
    return ∅
end



# 3.3 match non-commutative function
#     return iterator of matches
function match_sequence(ss, ps, fₐ=nothing, θ=(match_dict(),))
    #@show :ms, ss, ps, fₐ, collect(θ)
    n, m = length(ss), length(ps)
    nstar = count(is_segment, ps)
    m - nstar > n && return ∅ # total number of arguments required in the pattern
                              # exceeds the number of arguments in the subject.

    nplus = count(is_plus, ps)
    if !isnothing(fₐ)
        nplus += count(is_slot, ps) # count regular vars as plus vars
    end

    nfree = n - m + nstar
    nseq = nstar + nplus

    # For every distribution of free arguments in ss among the seq. vars,
    # the matches (θᵣ = θᵣ ∪ θ′)
    if nseq == 0 # one way, when ss and ps have the same length
        nfree == 0 || return ∅
        θ′ = _match_sequence1(ss, ps, fₐ, θ, n, ())
        return θ′ === nothing ? ∅ : θ′
    end
    _SeqMatches(multiexponents(nseq, nfree), ss, ps, fₐ, θ, n)
end

struct _SeqMatches{E,S,P,T,F}
    exps::E   # the distributions of the free arguments
    ss::S
    ps::P
    fₐ::F
    θ::T
    n::Int
end
Base.IteratorSize(::Type{<:_SeqMatches}) = Base.SizeUnknown()

# state: (state of exps, matches for the current distribution, their state)
function Base.iterate(it::_SeqMatches, st = (_Start(), (), _Start()))
    est, inner, ist = st
    while true
        r = ist isa _Start ? iterate(inner) : iterate(inner, ist)
        r === nothing || return (r[1], (est, inner, r[2]))
        re = est isa _Start ? iterate(it.exps) : iterate(it.exps, est)
        re === nothing && return nothing
        ks, est = re
        θ′ = _match_sequence1(it.ss, it.ps, it.fₐ, it.θ, it.n, ks)
        inner, ist = θ′ === nothing ? () : θ′, _Start()
    end
end

# the matches for one distribution ks of the free arguments, or nothing
function _match_sequence1(ss, ps, fₐ, θ, n, ks)
    i, j = 1, 1 # 0,0 in 0-based
    θ′ = θ
    for (l, pl) ∈ enumerate(ps)
        lsub = 1
        if (is_plus(pl) || is_segment(pl)) ||
            (is_slot(pl) && !isnothing(fₐ))

            kj = isempty(ks) ? 1 : ks[j]
            lsub = lsub + kj

            if is_segment(pl)
                lsub = lsub - 1
            end

            j = j + 1
        end
        ss′ = ss[i:(i+(lsub-1))] # lsub terms
        θ′ = match_one_to_one(ss′, pl, fₐ, θ′)
        (θ′ == ∅ || (θ′ isa Vector && isempty(θ′))) && break
        i = i + lsub
    end
    (θ′ == ∅ || (θ′ isa Vector && isempty(θ′))) && return nothing
    i == n + 1 || return nothing # all of ss must be consumed
    return θ′
end

## ---- commutative (associative when fₐ != nothing)

function match_commutative_sequence(ss, ps, fₐ = nothing, θ = (match_dict(),))
    #@show :mcs, ss, ps, fₐ,collect(θ)
    out = _match_constant_patterns(ss, ps)
    isnothing(out) && return ∅

    ss, ps = out

    # for each σ ∈ θ, the matches of the non-variable patterns; for each
    # of those, the matches of the regular variables; for each of those,
    # the matches of the sequence variables (depth first, lazily)
    _CommSeqMatches(θ, _anyvec(ss), ps, fₐ)
end

struct _Start end # an iterator not yet started

# a partial match: the subject terms and patterns left, and the match so far
const _Partial = Tuple{Vector{Any}, Any, MatchDict}

_anyvec(ss::Vector{Any}) = ss
_anyvec(ss) = Any[s for s ∈ ss]


# return trimmed ss, ps or nothing
function _match_constant_patterns(ss, ps)
    #@show :mcp, ss, ps
    Pconst = filter(!has_𝑋, ps)
    ss′ = ss
    for p ∈ Pconst      # check Pconst ⊂ ss (as multisets), else return nothing
        j = findfirst(s -> _eq_constant(s, p), ss′)
        isnothing(j) && return nothing
        ss′ = _deleteat(ss′, j) # remove only one copy
    end
    ps′ = filter(p -> p ∉ Pconst, ps)
    return (ss′, ps′)
end

# does subject term s equal constant pattern p?
# a symbol in a pattern may be a symbolic variable (non Symbol) in the subject
_eq_constant(s, p::Symbol) = Symbol(s) == p
_eq_constant(s, p) = isequal(s, p)

# trims down ss, ps
# return trimmed ss, ps or nothing
function _match_matched_variables(ss, ps, σ, fₐ=nothing)
    #@show :mmv, ss, ps, σ

    # subtract from, ps, ss previously matched variables
    (isnothing(σ) || isempty(σ)) && return (ss, ps)
    ps′, psₒ = _groupby(is_𝑋, ps)
    ps′′ = varname.(ps′)
    for (p,s) ∈ σ
        ind = findall(==(p), ps′′)
        for i ∈ ind
            v = ps′[i]
            itr = s
            if is_slot(v) || is_defslot(v)
                # in an associative context the subject is flattened, so
                # a value fₐ(a,b) bound elsewhere appears as a, b
                itr = (s,)
                if isassociative(fₐ) && iscall(s) && _opsym(operation(s)) == _opsym(fₐ) &&
                    isnothing(findfirst(isequal(s), ss))
                    itr = arguments(s)
                end
            end
            for sᵢ ∈ itr
                j = findfirst(isequal(sᵢ), ss) # `==` may not give a Bool
                isnothing(j) && return nothing
                ss = _deleteat(ss, j)
            end
        end
    end

    ps′′′ = vcat(psₒ, [v for v in ps′ if varname(v) ∉ keys(σ)])
    ss, ps′′′

end

# match non_variable_patterns
# return iterator of (ss, ps, σ) or nothing
function _match_non_variable_patterns(ss, ps, fₐ=nothing, σ=match_dict())
    #@show :mnvp, ss, ps, fₐ, σ

    out = _match_matched_variables(ss, ps, σ, fₐ)
    isnothing(out) && return nothing
    ss, ps = out
    ps′, ps′′ = _groupby(!is_𝑋, ps)

    n = length(ps′)
    n == 0 && return _Partial[(_anyvec(ss), ps, σ)]
    n ≤ length(ss) || return nothing

    # combinations of positions. Combinations with the same values give
    # the same matches, so only distinct ones are used: equal values share
    # an id, distinct combinations of ids are mapped back to positions.
    ids = Int[findfirst(isequal(s), ss) for s ∈ ss]
    combos = Vector{Int}[_ids_to_positions(c, ids) for c ∈ multiset_combinations(ids, n)]
    return _NonVarMatches(combos, _anyvec(ss), ps′, ps′′, σ, fₐ)
end

# The matches of the non-variable patterns, lazily: for each combination of
# subject terms, all the ways to match them to the patterns.
struct _NonVarMatches
    combos::Vector{Vector{Int}}
    ss::Vector{Any}
    ps′::Any    # the non-variable patterns
    ps′′::Any   # the others
    σ::MatchDict
    fₐ::Any
end
Base.IteratorSize(::Type{_NonVarMatches}) = Base.SizeUnknown()
Base.eltype(::Type{_NonVarMatches}) = _Partial

# state: (next combination, matches of the current one, next of those)
function Base.iterate(it::_NonVarMatches, st = (1, _Partial[], 1))
    k, buf, i = st
    while i > length(buf)
        k > length(it.combos) && return nothing
        buf, i = _nonvar_perms(it.combos[k], it.ps′, it.ps′′, it.σ, it.ss, it.fₐ), 1
        k += 1
    end
    return (buf[i], (k, buf, i + 1))
end

# we want to match over same size so we first pick combinations of
# size n, ss′, and then use a stack-based approach to loop over
# permutations of ss′ allowing for early termination if no
# matches are possible.
# (basic algorithm, with errors fixed, from claude on depth-first stack approach to compute
# permutations)
function _nonvar_perms(inds, ps′, ps′′, σ, ss, fₐ)
    ss′ = Any[ss[i] for i ∈ inds] # not ss[inds], which some argument types lack
    result = Tuple{Vector{Any}, Any, MatchDict}[]
    # (matched, remaining, matches so far); the matches are collected at
    # each step, as every branch below uses them and all are kept
    stack = Tuple{Vector{Any}, Vector{Any}, Vector{MatchDict}}[(Any[], ss′, MatchDict[σ])]
    while !isempty(stack)
        current, remaining, θ = pop!(stack)
        j = length(current)
        if j > 0

            p, s = ps′[j], current[end]
            p, θ′ = check_nonmatching_defslot(s, p, θ)
            θ = θ′ === θ ? θ : _collect_matches(θ′)
            p = normalize_pattern(p,s) # rewrite pattern if needed

            # normalize might make p a non call, if so ...
            if is_𝑋(p)
                pass_any_guard(p, s) || continue
                σ′ = match_dict(varname(p) => s)
                θ = union_merge(θ, σ′)
            else
                opₚ = operation(p) # s may not be a call (defslots)
                opₛ = nothing
                if iscall(s)
                    if is_𝑋(opₚ) # check for variable function head
                        opₛ = operation(s)
                        σ′ = match_dict(varname(opₚ) => opₛ)
                        θ = union_merge(θ, σ′)
                    elseif !any(is_defslot, arguments(p))
                        opₛ = first(normalize_subject(s, p))
                        _opsym(opₛ) === opₚ || continue # stop this track
                    end
                end
                θ = _collect_matches(match_one_to_one([s], p, fₐ, θ))
                isempty(θ) && continue # stop this track
            end
        end

        if isempty(remaining) # terminate successfully if nothing left in remaining
            ss′′ = Any[ss[i] for i ∈ setdiff(eachindex(ss), inds)] # by position, keeps repeats
            for σ ∈ θ
                push!(result, (ss′′, ps′′, σ))
            end
            continue
        end

        for i in reverse(eachindex(remaining)) # LIFO stack, reversing keeps order
            v = remaining[i]
            # equal values give the same permutations; use first only
            _any_equal(v, remaining, i - 1) && continue
            remaining′ = Any[remaining[k] for k ∈ eachindex(remaining) if k != i]
            push!(stack, (push!(copy(current), v), remaining′, θ))
        end

    end
    return result
end



# does p have a defslot that doesn't match at the operation level, then try and fix
# before the operations don't match
function check_nonmatching_defslot(s, p, θ′)
    #@show :cnd, s, p
    if iscall(p)
        opₚ = operation(p)
        if (!iscall(s) || (_opsym(operation(s)) != opₚ))
            if opₚ ∈ (:+, :*)
                argsₚ = arguments(p)
                inds = findall(is_defslot, argsₚ)
                if !isempty(inds)
                    val = defslot_op_map[opₚ]
                    σ′ = match_dict((varname.(argsₚ[inds]) .=> val)...) # no check for uniqueness of slot name
                    θ′ = union_merge(θ′, σ′)

                    ps = argsₚ[setdiff(eachindex(argsₚ), inds)]
                    p′ = pterm(opₚ, ps)
                    return p′, θ′
                end
            elseif opₚ == :^
                a,b = arguments(p)
                if is_defslot(b)
                    val = defslot_op_map[opₚ]
                    σ′ = match_dict(varname(b) => val)
                    θ′ = union_merge(θ′, σ′)
                    p′ = a
                    return p′, θ′
                end
            end
        end
    end
    return p, θ′
end


# match ~x type variables
# return an iterable of (ss, ps, σ)
function _match_regular_variables(ss, ps, fₐ=nothing, σ = match_dict())
    #@show :mrv, ss, ps, fₐ, σ
    isempty(ps) && return isempty(ss) ? _regvars((_anyvec(ss), ps, σ)) : _NOREGVARS

    out =  _match_matched_variables(ss, ps, σ, fₐ)
    isnothing(out) && return _NOREGVARS

    ss, ps = out
    # star variables may be empty, others need at least one term
    isempty(ss) && any(_needs_term, ps) && return _NOREGVARS

    # fₐ is  commutative, maybe associative
    isassociative(fₐ) && return _regvars((_anyvec(ss), ps, σ)) # associative turns ~x into ~~x


    ps_reg, ps′′ = _groupby(is_slot, ps)
    isempty(ps_reg) && return _regvars((_anyvec(ss), ps, σ))

    if length(ps_reg) < length(ss)
        if ps_reg == ps
            # can't match, not enough
            return _NOREGVARS
        end
    end

    return _RegVarMatches(nothing, _countmap(ss), _countmap(ps_reg), σ, ps′′)
end

# The matches of the regular variables, lazily (a guard may be costly, or
# throw): for each way to give each variable a distinct subject term (the
# first variable's choice changing fastest), the match and what is left.
struct _RegVarMatches
    fixed::Union{Nothing, Vector{_Partial}} # when not nothing, the matches
    ds::Vector     # subject term => count
    dp::Vector     # variable => count
    σ::MatchDict
    ps′′::Any      # the other patterns
end
Base.IteratorSize(::Type{_RegVarMatches}) = Base.SizeUnknown()
Base.eltype(::Type{_RegVarMatches}) = _Partial

_regvars(a::_Partial) = _RegVarMatches(_Partial[a], [], [], match_dict(), nothing)
const _NOREGVARS = _RegVarMatches(_Partial[], [], [], match_dict(), nothing)

# the state, the choices (or for fixed matches, the index), is updated in place
function Base.iterate(it::_RegVarMatches, st::Union{Nothing,Vector{Int}} = nothing)
    fixed = it.fixed
    if fixed !== nothing
        i = st === nothing ? 1 : only(st) + 1
        i > length(fixed) && return nothing
        st === nothing ? (st = [i]) : (st[1] = i)
        return (fixed[i], st)
    end
    n = length(it.ds)
    if st === nothing
        n == 0 && return nothing
        inds = ones(Int, length(it.dp))
    else
        inds = st
        _next_choice!(inds, n) || return nothing
    end
    while true
        r = _split_take1(it.ds, it.dp, inds)
        if r !== nothing
            σ′, ds′ = r
            iscompatible(σ′, it.σ) &&
                return ((_uncountmap(ds′), it.ps′′, merge_match(it.σ, σ′)), inds)
        end
        _next_choice!(inds, n) || return nothing
    end
end

# the next choice, the first fastest; false after the last
function _next_choice!(inds, n)
    j = 1
    while j ≤ length(inds) && inds[j] == n
        inds[j] = 1
        j += 1
    end
    j > length(inds) && return false
    inds[j] += 1
    return true
end


# return iterator of matches or nothing
function _match_sequence_variables(ss, ps, fₐ=nothing, σ = match_dict())
    #@show :msv, ss, ps, fₐ, σ

    isempty(ps) && return isempty(ss) ? (σ, ) : ∅

    out =  _match_matched_variables(ss, ps, σ, fₐ)
    isnothing(out) && return nothing

    ss, ps = out
    isempty(ps) && return isempty(ss) ? (σ, ) : ∅
    isempty(ss) && any(_needs_term, ps) && return ∅

    if !isassociative(fₐ)
        !isempty(filter(is_slot, ps)) && return nothing
    end

    vs, vs′ = _groupby(x -> is_slot(x) || is_plus(x), ps)

    length(vs) > length(ss) && return nothing #(); too many plus variables

    ds = _countmap(ss)
    dplus, dstar = _countmap(vs), _countmap(vs′)

    vars = Any[first.(dplus)..., first.(dstar)...]
    isempty(vars) && return nothing

    svars = Any[first(d) for d ∈ ds]
    ks = Int[last.(dplus)..., last.(dstar)...]
    # for each distinct subject term, the ways to give its copies to the
    # variables, a_j copies to the jth with sum(a_j * ks[j]) == count
    choices = Vector{Vector{Int}}[_distribute_total(last(d), ks) for d ∈ ds]
    # a variable's terms are sorted (<ₑ); the order of the distinct terms is
    # found once (stable, as `sort` is) rather than for each assignment
    order = length(svars) ≤ 1 ? collect(eachindex(svars)) : sortperm(Symbol.(svars))

    return _SeqVarMatches(σ, vars, Symbol[varname(v) for v ∈ vars], svars, order,
                          choices, length(dplus), fₐ)
end

# Enumerate valid assignments of subject counts to sequence variables without
# constructing the huge cartesian product of all 0:s choices per variable.
# For a given subject count `total`, and per-variable weight `ks[j]`, choose
# counts `a_j` with sum(a_j * ks[j]) == total.
function _distribute_total(total::Int, ks::Vector{Int})
    n = length(ks)
    row = zeros(Int, n)
    out = Vector{Vector{Int}}()
    _distribute_total!(out, row, ks, n, total)
    out
end
function _distribute_total!(out, row, ks, j, remaining)
    if j < 1
        remaining == 0 && push!(out, copy(row))
        return
    end
    k = ks[j]
    for a in 0:fld(remaining, k)
        row[j] = a
        _distribute_total!(out, row, ks, j - 1, remaining - a * k)
    end
end

# The matches of the sequence variables, lazily: one for each choice, per
# distinct subject term, of how its copies are given to the variables (the
# product of `choices`, in reverse order), when every plus variable gets a
# term and the values pass the guards and agree with `σ`.
struct _SeqVarMatches
    σ::MatchDict
    vars::Vector{Any}       # plus (and, if associative, slot) variables, then the others
    names::Vector{Symbol}
    svars::Vector{Any}      # the distinct subject terms
    order::Vector{Int}      # svars in <ₑ order
    choices::Vector{Vector{Vector{Int}}}
    nplus::Int
    fₐ::Any
end
Base.IteratorSize(::Type{_SeqVarMatches}) = Base.SizeUnknown()
Base.eltype(::Type{_SeqVarMatches}) = MatchDict

function Base.iterate(it::_SeqVarMatches, idx::Union{Nothing,Vector{Int}} = nothing)
    if idx === nothing
        # start at the last element of the product
        any(isempty, it.choices) && return nothing
        idx = Int[length(c) for c ∈ it.choices]
        σ′ = _seqvar_match(it, idx)
        σ′ === nothing || return (σ′, idx)
    end
    while _prev!(idx, it.choices)
        σ′ = _seqvar_match(it, idx)
        σ′ === nothing || return (σ′, idx)
    end
    return nothing
end

# step back through the product, the first index fastest
function _prev!(idx, choices)
    for i ∈ eachindex(idx)
        if idx[i] > 1
            idx[i] -= 1
            return true
        end
        idx[i] = length(choices[i])
    end
    return false
end

function _seqvar_match(it::_SeqVarMatches, idx)
    choices = it.choices
    for j ∈ 1:it.nplus # a plus variable needs a term
        any(i -> choices[i][idx[i]][j] > 0, eachindex(idx)) || return nothing
    end
    fₐ = it.fₐ
    σ′ = it.σ
    for (j, v) ∈ enumerate(it.vars)
        vv = Any[]
        for i ∈ it.order
            for _ ∈ 1:choices[i][idx[i]][j]
                push!(vv, it.svars[i])
            end
        end
        # give defaults; nothing or value
        if isempty(vv)
            if is_defslot(v)
                vv′ = defslot_op_map[fₐ]
            elseif is_segment(v)
                vv′ = Any[] #()
            else
                vv′ = nothing
            end
        else
            # if var is ~x fₐ not nothing call fₐ on vv
            vv′ = (is_slot(v) && !isa(fₐ, Nothing)) ? sterm(fₐ, vv) : vv
        end
        if !isnothing(vv′)
            pass_any_guard(v, vv′) || return nothing
            k = it.names[j]
            vv′ = isa(vv′, Number) ? unwrap_const(vv′) : vv′
            old = get(σ′, k, _NOKEY)
            if old === _NOKEY
                σ′ = MatchDict(σ′, k, vv′)
            elseif !isequal(old, vv′)
                return nothing
            end
        end
    end
    iscompatible(it.σ, σ′) || return nothing
    return merge_match(it.σ, σ′)
end

# The matches of a commutative sequence; see match_commutative_sequence
struct _CommSeqMatches{T}
    θ::T
    ss::Vector{Any}
    ps::Any
    fₐ::Any
end
Base.IteratorSize(::Type{<:_CommSeqMatches}) = Base.SizeUnknown()
Base.eltype(::Type{<:_CommSeqMatches}) = MatchDict


# where the depth-first search is; mutated by `iterate`
mutable struct _CommSeqCursor
    θstate::Any                       # state of θ, or _Start()
    s1::Any                           # the non-variable pattern matches
    s1state::Any                      # its state, or _Start()
    s2::_RegVarMatches                # the regular variable matches
    s2state::Union{Nothing, Vector{Int}} # their state, or nothing
    s3::Union{Nothing,_SeqVarMatches} # the sequence variable matches
    s3state::Union{Nothing,Vector{Int}}
end

function Base.iterate(it::_CommSeqMatches,
                      c::_CommSeqCursor = _CommSeqCursor(_Start(), nothing, _Start(),
                                                         _NOREGVARS, nothing, nothing, nothing))
    while true
        s3, s3state = c.s3, c.s3state
        if s3 !== nothing
            r = s3state === nothing ? iterate(s3) : iterate(s3, s3state)
            if r !== nothing
                c.s3state = r[2]
                return (r[1], c)
            end
            c.s3 = nothing
        end
        s2, s2state = c.s2, c.s2state
        r2 = s2state === nothing ? iterate(s2) : iterate(s2, s2state)
        if r2 === nothing
            c.s2, c.s2state = _NOREGVARS, nothing # done; don't iterate it again
        else
            (ss, ps, σ), c.s2state = r2
            r3 = _match_sequence_variables(ss, ps, it.fₐ, σ)
            if r3 isa _SeqVarMatches
                c.s3, c.s3state = r3, nothing
            elseif r3 isa Tuple{MatchDict}
                return (r3[1], c)
            end
            continue
        end
        if c.s1 !== nothing
            r = c.s1state isa _Start ? iterate(c.s1) : iterate(c.s1, c.s1state)
            if r !== nothing
                a, c.s1state = r
                ss, ps, σ = a
                c.s2, c.s2state = _match_regular_variables(ss, ps, it.fₐ, σ), nothing
                continue
            end
            c.s1 = nothing
        end
        r = c.θstate isa _Start ? iterate(it.θ) : iterate(it.θ, c.θstate)
        r === nothing && return nothing
        σ, c.θstate = r
        c.s1, c.s1state = _match_non_variable_patterns(it.ss, it.ps, it.fₐ, σ), _Start()
    end
end

## --- utilities
# the matches of an iterable of matches, as a vector
_collect_matches(θ::Vector{MatchDict}) = θ
_collect_matches(θ) = MatchDict[σ for σ ∈ θ]

# is v equal to one of xs[1:n]?
function _any_equal(v, xs, n)
    for k ∈ 1:n
        isequal(v, xs[k]) && return true
    end
    return false
end

# does pattern need at least one subject term? (star and default variables do not)
_needs_term(p) = !(is_segment(p) || is_defslot(p))

# positions in ss for a combination c of ids (ids[k] is the id of ss[k]),
# using the first unused position with each id
function _ids_to_positions(c, ids)
    inds = Int[]
    for id ∈ c
        push!(inds, findfirst(k -> ids[k] == id && k ∉ inds, eachindex(ids)))
    end
    inds
end

# remove ith element; tuple friendly
_deleteat(ss, j) = [ss[i] for i in eachindex(ss) if i != j]

# combine via union but filter out nothing values
function _chain(i)
    ii= Iterators.filter(!isnothing, i)
    iii = Iterators.flatten(ii)
    iii
end

# counting functions
function _countmap(x)
    d = Dict{Any,Int}() # the order of a Dict{Any,Any}: same keys, same slots
    for xi in x
        d[xi] = get(d, xi, 0) + 1
    end
    return [k => v for (k,v) ∈ d]
end
function _uncountmap(dx)
    return Any[k for (k,v) ∈ dx for _ ∈ 1:v]
end

# a way to grab the pie: give the ith variable of dp the inds[i]th term of ds
function _split_take1(ds, dp, inds)
    ds′ = copy(ds)
    σ = match_dict()
    for (i, (p, np)) ∈ zip(inds, (dp))
        s, ns = ds′[i]
        np > ns && return nothing # won't fit
        pass_any_guard(p, s) || return nothing
        σ′ = match_dict(varname(p) => s)
        # same variable may appear with and without a guard
        iscompatible(σ, σ′) || return nothing
        ds′[i] = s => (ns - np)
        σ = merge_match(σ, σ′)
    end
    (σ, ds′)
end


# normalize pattern
# |   sub   | pat  | pat′
# |---------|------|-------
# | sqrt    |  ^   | sqrt
# | ^(1//2) | sqrt | ^(1//2)
# | ^(1//3) | cbrt | ^(1//3)
# | ^(-1)   |  /   | ^(-1)
# | ^(-1//2)| 1/sqrt | ^(-1//2)
# | e^      | exp  | e^
# | exp     | e^...| exp(...)
# |  /      | ^(-1)| /
# |  *      |  /   | *
# the value of a constant, also for an expression holding a number, e.g. :(1//2)
_constant_value(x) = unwrap_const(x)
_constant_value(x::Expr) = _isnumber(x) ? eval(x) : x
_isnumber(::Any) = false
_isnumber(x::Number) = true
_isnumber(x::Symbol) = isa(unwrap_const(x), Number)
_isnumber(x::Expr) = !(_ismatch(x, !_isnumber))

function normalize_pattern(pat, sub)
    iscall(sub) || return pat
    iscall(pat) || return pat # are there no op examples?
    opₚ = operation(pat)
    opₚ isa Symbol || return pat # e.g. (~F)(...); no rewrite applies
    opₛ = _opsym(operation(sub))::Symbol

    if opₛ === :sqrt && opₚ === :^
        u, v = arguments(pat)
        if isequal(_constant_value(v), 1//2)
            return Expr(:call, :sqrt, u)
        end
    elseif opₛ === :cbrt && opₚ === :^
        u, v = arguments(pat)
        if isequal(_constant_value(v), 1//3)
            return Expr(:call, :cbrt, u)
        end
    elseif opₛ === :^ && opₚ === :sqrt
        a, b = arguments(sub)
        if isequal(_constant_value(b), 1//2)
            v = only(arguments(pat))
            return Expr(:call, :^, v, b) # b, not 1//2, compares equal to itself
        end
    elseif opₛ === :^ && opₚ === :cbrt
        a, b = arguments(sub)
        if isequal(_constant_value(b), 1//3)
            v = only(arguments(pat))
            return Expr(:call, :^, v, b) # b, not 1//2, compares equal to itself
        end
    elseif opₛ === :^ && opₚ === :/
        a, b = arguments(sub)
        u, v = arguments(pat)
        if unwrap_const(u) == 1
            if is_operation(:^)(v)
                w,y = arguments(v)
                y′ = _constant_value(y)
                isa(y′, Number) || return pat # can't negate a symbolic exponent
                return Expr(:call, :^, w, -y′)
            elseif is_operation(:sqrt)(v) && isequal(_constant_value(b), -1//2)
                # `isequal`, not `<`, as a symbolic exponent may not compare
                return Expr(:call, :^, only(arguments(v)), b)
            else
                return Expr(:call, :^, v, -1)
            end
        end
    elseif opₛ === :^ && opₚ === :exp
        a, b = arguments(sub)
        if Symbol(unwrap_const(a)) == :ℯ
            v = only(arguments(pat))
            return Expr(:call, :^, ℯ, v)
        end
    elseif opₛ === :exp && opₚ === :^
        u,v = arguments(pat)
        if eq_expr(u, :ℯ)
            return Expr(:call, :exp, v)
        end
    elseif opₛ === :/ && opₚ === :^
        u,v = arguments(pat)
        if isequal(_constant_value(v), -1)
            return Expr(:call, :/, 1, u)
        end
    elseif opₛ === :* && opₚ === :/
        u, v = arguments(pat)
        return Expr(:call, :*, u, _invert_expr(v))
    end
    return pat
end

# normalize subject
# when the pattern is a power, or a product with a power, a subject in another
# form is matched as one: the operation and arguments matched are
# |   pat      |   sub     | op, args
# |------------|-----------|-----------
# | ^          | sqrt(u)   | ^, (u, 1//2)
# | ^          | exp(u)    | ^, (ℯ, u)
# | ^          | 1/u^k     | ^, (u, -k)
# | ^          | 1/sqrt(u) | ^, (u, -1//2)
# | ^          | 1/exp(u)  | ^, (ℯ, -u)
# | ^          | 1/u       | ^, (u, -1)
# | * with a ^ | u/v       | *, factors of u and the inverted factors of v
# The arguments are matched directly, so no term is built which a symbolic
# package might simplify back, e.g. u^(1//2) to sqrt(u).
function normalize_subject(sub, pat)
    opₛ, args = operation(sub), arguments(sub)
    iscall(pat) || return (opₛ, args)
    opₚ, op = operation(pat), _opsym(opₛ)
    if opₚ == :^
        op == :sqrt && return (:^, Any[only(args), 1//2])
        op == :exp && return (:^, Any[ℯ, only(args)])
        if op == :/ && _isone(_unwrap_const(first(args)))
            v = last(args)
            iscall(v) || return (:^, Any[v, -1])
            opᵥ = _opsym(operation(v))
            opᵥ == :^ && return (:^, Any[first(arguments(v)), _negate(last(arguments(v)))])
            opᵥ == :sqrt && return (:^, Any[only(arguments(v)), -1//2])
            opᵥ == :exp && return (:^, Any[ℯ, _negate(only(arguments(v)))])
            return (:^, Any[v, -1])
        end
    elseif opₚ == :* && op == :/ && any(is_operation(:^), arguments(pat))
        return (:*, _data_as_powers(sub))
    end
    return (opₛ, args)
end

# ----- default slot code ------
# set defslots to default value specified in inds′
# return adjusted ps and σ′ containing set default values
function set_defslots(ps, opₚ, inds, inds′)
    # we use default for inds′, nondefault for others
    ps′ = copy(ps)
    σ′ = match_dict()
    for j ∈ reverse(sort(inds′)) # to avoid deletion in ps′
        i′ = inds[j]
        pᵢ = ps[i′]
        # p is ~!x or (a)^(~!x)
        if is_defslot(pᵢ)
            ps′ = vcat(ps′[1:i′-1], ps′[i′+1:end])
            defval = defslot_op_map[opₚ]
            σ′ = match_dict(σ′, varname(pᵢ) => defval)
        else
            # power
            a, b = arguments(pᵢ)
            ps′ = vcat(ps′[1:i′-1], a, ps′[i′+1:end])
            defval = defslot_op_map[:^]
            σ′ = match_dict(σ′, varname(b) => defval)
        end
    end
    # replace defslot with slot
    for j in setdiff(eachindex(inds), inds′)
        i′ = inds[j]
        pᵢ = ps[i′]
        if is_defslot(pᵢ)
            pᵢ′ = _defslot_to_slot(pᵢ)
        else
            a, b = arguments(pᵢ)
            pᵢ′ = Expr(:call, :^, a, _defslot_to_slot(b))
        end
        # replace in ps′ which may be shorter than ps
        i = findall(==(pᵢ), ps′)
        ps′[i] .= (pᵢ′,)
    end
    return (ps′, σ′)
end

# ~!x --> ~x, ~!x::pred --> ~x::pred (keeps any guard)
_defslot_to_slot(p) = Expr(:call, :~, p.args[2].args[2])

# This handles defslots by
# looping over all combinations of having the
# defslot be a slot variable *or* its default value.
# Matches using fewer defaults are preferred: the combinations are
# tried in groups by the number of defaults used and the union of
# the matches from the first group with any match is returned.
# A default exponent (n => 1) is not used when the base matches a power.
function clear_defslots(ss, p, fₐ, θ)
    #@show :cf, ss, p
    opₚ = operation(p)
    ps = arguments(p)
    inds = findall(has_defslot, ps)

    θ′′ = MatchDict[]
    nmatched = nothing # number of defaults used by the matches in θ′′
    for inds′ = powerset(1:length(inds)) # ordered by length(inds′)
        !isnothing(nmatched) && length(inds′) > nmatched && break
        ps′, σ′ = set_defslots(ps, opₚ, inds, inds′)
        isempty(ps′) && continue # all defaults; no pattern left to match
        p′ = pterm(opₚ, ps′)
        θ′ = union_merge(θ, σ′)
        # might need to adjust fₐ; p′ may no longer be a call
        fₐ′ = fₐ
        if opₚ == :^ && !is_operation(:^)(p′)
            fₐ′ = nothing
        end
        itr = match_one_to_one(ss, p′, fₐ′, θ′)
        isnothing(itr) && continue
        vars = _defaulted_power_bases(ps, opₚ, inds, inds′)
        if !isempty(vars)
            itr = (σ for σ ∈ itr if !any(v -> haskey(σ, v) && _is_power(σ[v]), vars))
        end
        r = iterate(itr) # find the first match once, rather than by `isempty` and again later
        r === nothing && continue
        itr′ = _Peeled(r[1], itr, r[2], false)
        isempty(inds′) && return itr′ # no defaults needed
        nmatched = length(inds′)
        θ′′ = union(θ′′, itr′)
    end

    return θ′′

end

# an iterator with its first element and the state after it already found.
# Iterated again from the start, the iterator is iterated afresh, as a state
# may be updated in place by `iterate`.
mutable struct _Peeled{I,S}
    first::Any
    rest::I
    st::S
    used::Bool
end
Base.IteratorSize(::Type{<:_Peeled}) = Base.SizeUnknown()
Base.eltype(::Type{_Peeled{I,S}}) where {I,S} = eltype(I)
function Base.iterate(p::_Peeled)
    p.used && return iterate(p.rest)
    p.used = true
    return (p.first, p.st)
end
Base.iterate(p::_Peeled, st) = iterate(p.rest, st)

# names of variable bases of powers whose exponent is set to its default
function _defaulted_power_bases(ps, opₚ, inds, inds′)
    vars = Symbol[]
    for j ∈ inds′
        pᵢ = ps[inds[j]]
        if is_defslot(pᵢ)
            opₚ == :^ || continue   # ~!x in a sum or product
            base = first(ps)        # p is a^(~!x)
        else
            base = first(arguments(pᵢ)) # pᵢ is a^(~!x)
        end
        is_𝑋(base) && push!(vars, varname(base))
    end
    vars
end

_is_power(x) = iscall(x) && _opsym(operation(x)) == :^
