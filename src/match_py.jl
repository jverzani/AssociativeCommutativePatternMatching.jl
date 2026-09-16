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
        opₛ, opₚ = operation(s), operation(p)
        if is_𝑋(opₚ) # check for variable function head
            σ′ = match_dict(varname(opₚ) => opₛ)
            θ = (merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
        else
            Symbol(opₛ) == opₚ || return ∅ # can't have defslot in p at this level
        end
        ss, ps = arguments(s), arguments(p)
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

    λ = ks -> begin
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
            θ′ == ∅  && break
            i = i + lsub
        end
        θ′ == ∅ && return nothing
        return θ′
    end

    i = multiexponents(nseq, nfree) # For every distribution of free arguments
                                    # in ss among the seq. vars...
    ii = Iterators.map(λ, i)
    _chain(ii)                      # θᵣ = θᵣ ∪ θ′
end

## ---- commutative (associative when fₐ != nothing)

function match_commutative_sequence(ss, ps, fₐ = nothing, θ = (match_dict(),))
    #@show :mcs, ss, ps, fₐ,collect(θ)
    out = _match_constant_patterns(ss, ps)
    isnothing(out) && return ∅

    ss, ps = out

    ## chain together
    i = let ss=ss, ps=ps
        Iterators.map(σ -> (ss, ps, σ), θ)
    end

    ii = Iterators.map(i) do a
        ss, ps, σ = a
        itr = _match_non_variable_patterns(ss, ps, fₐ, σ)
        itr
    end |> _chain

    iii = Iterators.map(ii) do a
        ss, ps, σ = a
        itr = _match_regular_variables(ss, ps, fₐ, σ)
        itr
    end |> _chain

    iv = Iterators.map(iii) do a
        ss, ps, σ = a
        itr = _match_sequence_variables(ss, ps, fₐ, σ)
    end |> _chain

end

# return trimmed ss, ps or nothing
function _match_constant_patterns(ss, ps)
    #@show :mcp, ss, ps
    Pconst = filter(!has_𝑋, ps)
    ss′ = ss
    for p ∈ Pconst      # check Pconst ⊂ ss, else return nothing
        if isa(p, Symbol)
            p in Symbol.(ss′) || return nothing
            ss′ = filter(s -> !=(Symbol(s), p), ss′)
        else
            p in ss′ || return nothing
            ss′ = filter(!=(p), ss′)
        end
    end
    ps′ = filter(p -> p ∉ Pconst, ps)
    return (ss′, ps′)
end

# trims down ss, ps
# return trimmed ss, ps or nothing
function _match_matched_variables(ss, ps, σ)
    #@show :mmv, ss, ps, σ

    # subtract from, ps, ss previously matched variables
    (isnothing(σ) || isempty(σ)) && return (ss, ps)
    ps′, psₒ = _groupby(is_𝑋, ps)
    ps′′ = varname.(ps′)
    for (p,s) ∈ σ
        ind = findall(==(p), ps′′)
        for i ∈ ind
            v = ps′[i]
            itr = (is_slot(v) || is_defslot(v)) ? (s,) : s
            for sᵢ ∈ itr
                j = findfirst(==(sᵢ), ss)
                isnothing(j) && return nothing
                ss = vcat(ss[1:(j-1)], ss[(j+1):end])
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

    out = _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing
    ss, ps = out
    ps′, ps′′ = _groupby(!is_𝑋, ps)

    n = length(ps′)
    n == 0 && return ((ss, ps, σ), )
    n ≤ length(ss) || return nothing

    # we want to match over same size so we first pick combinations of
    # size n, ss′, and then use a stack-based approach to loop over
    # permutations of ss′ allowing for early termination if no
    # matches are possible.
    # (basic algorithm, with errors fixed, from claude on depth-first stack approach to compute
    # permutations)
    λ = (ss′, ps′, σ, ss) -> begin
        result = Any[]
        stack = Any[([], ss′, [σ])]
        while !isempty(stack)
            current, remaining, θ = pop!(stack)
            j = length(current)
            if j > 0

                p, s = ps′[j], current[end]
                p, θ = check_nonmatching_defslot(s, p, θ)
                p = normalize_pattern(p,s) # rewrite pattern if needed

                # normalize might make p a non call, if so ...
                if is_𝑋(p)
                    pass_any_guard(p, s) || continue
                    σ′ = match_dict(varname(p) => s)
                    θ = (merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
                else
                    opₚ = operation(p) # s may not be a call (defslots)
                    opₛ = nothing
                    if iscall(s)
                        if is_𝑋(opₚ) # check for variable function head
                            opₛ = operation(s)
                            σ′ = match_dict(varname(opₚ) => opₛ)
                            θ = (merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
                        elseif !any(is_defslot, arguments(p))
                            opₛ = operation(s)
                            Symbol(opₛ) == opₚ || continue # stop this track
                        end
                    end
                    θ = match_one_to_one([s], p, fₐ, θ)
                    isempty(θ) && continue # stop this track
                end
            end

            if isempty(remaining) # terminate successfully if nothing left in remaining
                ss′′ = setdiff(ss, ss′)
                for σ ∈ θ
                    push!(result, (ss′′, ps′′, σ))
                end
                continue
            end

            for i in reverse(eachindex(remaining)) # LIFO stack, reversing keeps order
                v = remaining[i]
                remaining′ = deleteat!(copy(remaining), i)
                val = (vcat(current, v),
                       remaining′,
                       θ)
                push!(stack, val)
            end

        end
        return result
    end

    i = combinations(ss, n)
    ii = Iterators.map(ss′ -> λ(ss′, ps′, σ, ss), i)
    iii = Iterators.flatten(ii)
    return iii
end



# does p have a defslot that doesn't match at the operation level, then try and fix
# before the operations don't match
function check_nonmatching_defslot(s, p, θ′)
    #@show :cnd, s, p
    if iscall(p)
        opₚ = operation(p)
        if (!iscall(s) || (Symbol(operation(s)) != opₚ))
            if opₚ ∈ (:+, :*)
                argsₚ = arguments(p)
                inds = findall(is_defslot, argsₚ)
                if !isempty(inds)
                    val = defslot_op_map[opₚ]
                    σ′ = match_dict((varname.(argsₚ[inds]) .=> val)...) # no check for uniqueness of slot name
                    θ′ = (merge_match(σ, σ′) for σ ∈ θ′ if iscompatible(σ, σ′))

                    ps = argsₚ[setdiff(eachindex(argsₚ), inds)]
                    p′ = pterm(opₚ, ps)
                    return p′, θ′
                end
            elseif opₚ == :^
                a,b = arguments(p)
                if is_defslot(b)
                    val = defslot_op_map[opₚ]
                    σ′ = match_dict(varname(b) => val)
                    θ′ = (merge_match(σ, σ′) for σ ∈ θ′)
                    p′ = a
                    return p′, θ′
                end
            end
        end
    end
    return p, θ′
end


# match ~x type variables
# return iterator of (ss, ps, σ)
function _match_regular_variables(ss, ps, fₐ=nothing, σ = match_dict())
    #@show :mrv, ss, ps, fₐ, σ
    isempty(ps) && !isempty(ss) && return ∅
    isempty(ss) && !isempty(ps) && return ∅

    isempty(ps) && return ((ss, ps, σ),)

    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return ∅

    ss, ps = out

    # fₐ is  commutative, maybe associative
    isassociative(fₐ) && return ((ss, ps, σ),) # associative turns ~x into ~~x


    ps_reg, ps′′ = _groupby(is_slot, ps)
    isempty(ps_reg) && return ((ss, ps, σ),)

    if length(ps_reg) < length(ss)
        if ps_reg == ps
            # can't match, not enough
            return ∅
        end
    end

    dp = _countmap(ps_reg)
    ds = _countmap(ss)
    i = _split_take(ds, dp)

    ii = Iterators.filter(ab -> begin
                          iscompatible(first(ab), σ)
                          end, i)

    iii = Iterators.map(ii) do (σ′, ds)
        σ′ = merge_match(σ, σ′)
        ss′′ = _uncountmap(ds)
        (ss′′, ps′′, σ′)
    end

    return iii
end


# return iterator of matches or nothing
function _match_sequence_variables(ss, ps, fₐ=nothing, σ = match_dict())
    #@show :msv, ss, ps, fₐ, σ

    isempty(ps) && !isempty(ss) && return ∅
    isempty(ss) && !isempty(ps) && return ∅

    isempty(ps) && return (σ, )

    out =  _match_matched_variables(ss, ps, σ)
    isnothing(out) && return nothing

    ss, ps = out

    if !isassociative(fₐ)
        !isempty(filter(is_slot, ps)) && return nothing
    end

    vs, vs′ = _groupby(x -> is_slot(x) || is_plus(x), ps)

    length(vs) > length(ss) && return nothing #(); too many plus variables

    ds = _countmap(ss)
    dplus, dstar = _countmap(vs), _countmap(vs′)

    vars = vcat(first.(dplus), first.(dstar))
    isempty(vars) && return nothing

    svars = first.(ds)

    pluses = last.(dplus)
    stars = last.(dstar)
    ks = vcat(pluses, stars)

    n1, n2 = length(pluses), length(stars)
    n = n1 + n2

    h = isnothing(fₐ) ? identity :
        (as) -> pterm(fₐ, as)

    # rename
    ssᵥ = [v for (k,v) in ds] # last.(ds)

    # Enumerate valid assignments of subject counts to sequence variables without
    # constructing the huge cartesian product of all 0:s choices per variable.
    # For a given subject count `total`, and per-variable weight `ks[j]`, choose
    # counts `a_j` with sum(a_j * ks[j]) == total.
    function _distribute_total(total, ks)
        n = length(ks)
        row = zeros(Int, n)
        out = Vector{Vector{Int}}()
        function rec(j, remaining)
            if j > n
                remaining == 0 && push!(out, copy(row))
                return
            end
            k = ks[j]
            maxv = fld(remaining, k)
            for a in 0:maxv
                row[j] = a
                rec(j + 1, remaining - a * k)
            end
        end
        rec(1, total)
        out
    end

    ii = Iterators.filter(Iterators.product((_distribute_total(s, ks) for s in ssᵥ)...)) do u
        all(sum(ui .* ks) == si for (ui, si) in zip(u, ssᵥ)) &&
            all(sum(ui[i] for ui in u) > 0 for i in 1:n1)
    end

    iii = Iterators.map(Iterators.reverse(ii)) do u
        σ′ = σ
        for (j, v) ∈ enumerate(vars)
            vv = []
            for (i,s) in enumerate(svars)
                for _ in 1:u[i][j]
                    push!(vv, s) # allocates less than appending repeat([s],uᵢⱼ)
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
                vv = sort(vv, lt = <ₑ)
                vv′ = (is_slot(v) && !isa(fₐ, Nothing)) ? sterm(fₐ, vv) : vv
            end
            if !isnothing(vv′)

                pass_any_guard(v, vv′) || return nothing

                var = varname(v)
                σ′′ = match_dict(var => vv′)
                iscompatible(σ′, σ′′) || return nothing
                σ′ = merge_match(σ′, σ′′)
            end
        end
        iscompatible(σ, σ′) || return nothing
        return merge_match(σ, σ′)
    end

    iv = Iterators.filter(!isnothing, iii)
    iv
end

## --- utilities
# combine via union but filter out nothing values
function _chain(i)
    ii= Iterators.filter(!isnothing, i)
    iii = Iterators.flatten(ii)
    iii
end

# counting functions
function _countmap(x)
    d = Dict()
    [(d[xi] = get(d, xi, 0) + 1) for xi in x]
    return [k => v for (k,v) ∈ d]
end
function _uncountmap(dx)
    return vcat((repeat([k],v) for (k,v) in dx)...)
end

# different ways to grab the pie
function _split_take(ds, dp)
    n = length(ds)
    k = length(dp)

    i = Iterators.product((1:n for _ in 1:k)...)
    ii = Iterators.map(i) do inds
        ds′ = copy(ds)
        σ = ∅
        for (i, (p, np)) ∈ zip(inds, (dp))
            s, ns = ds′[i]
            np > ns && (σ = ∅; break) # won't fit
            ds′[i] = s => (ns - np)
            σ = merge_match(σ, match_dict(varname(p) => s)) # XXX? Check compatible?
        end
        σ == ∅ && return nothing
        (σ, ds′)
    end
    iii = Iterators.filter(!isnothing, ii)
end


# normalize pattern
# |   sub   | pat  | pat′
# |---------|------|-------
# | sqrt    |  ^   | sqrt
# | ^(1//2) | sqrt | ^(1//2)
# | ^(1//3) | cbrt | ^(1//3)
# | ^(-1)   |  /   | ^(-1)
# | e^      | exp  | e^
# | exp     | e^...| exp(...)
# |  /      | ^(-1)| /
# |  *      |  /   | *
function normalize_pattern(pat, sub)
    iscall(sub) || return pat
    opₛ = Symbol(operation(sub))
    iscall(pat) || return pat # are there no op examples?
    opₚ = operation(pat)

    if (opₛ, opₚ) == (:sqrt, :^)
        u, v = arguments(pat)
        if eq_expr(v, :(1//2))
            return Expr(:call, :sqrt, u)
        end
    elseif (opₛ, opₚ) == (:cbrt, :^)
        u, v = arguments(pat)
        if eq_expr(v, :(1//3))
            return Expr(:call, :cbrt, u)
        end
    elseif (opₛ, opₚ) == (:^, :sqrt)
        a, b = arguments(sub)
        if unwrap_const(b) == 1//2
            v = only(arguments(pat))
            return Expr(:call, :^, v, Expr(:call, ://, 1,2))
        end
    elseif (opₛ, opₚ) == (:^, :cbrt)
        a, b = arguments(sub)
        if unwrap_const(b) == 1//3
            v = only(arguments(pat))
            return Expr(:call, :^, v, Expr(:call, ://, 1,3))
        end
    elseif (opₛ, opₚ) == (:^, :/)
        a, b = arguments(sub)
        b′ = unwrap_const(b)
        if isa(b′, Real) && b′ < 0 #unwrap_const(b) == -1
            u, v = arguments(pat)
            if unwrap_const(u) == 1
                if is_operation(:^)(v)
                    w,y = arguments(v)
                    p = Expr(:call, :^, w, -1*unwrap_const(y))
                else
                    p = Expr(:call, :^, v, -1)
                end
                return p
            end
        end
    elseif (opₛ, opₚ) == (:^, :exp)
        a, b = arguments(sub)
        if Symbol(unwrap_const(a)) == :ℯ
            v = only(arguments(pat))
            return Expr(:call, :^, ℯ, v)
        end
    elseif (opₛ, opₚ) == (:exp, :^)
        u,v = arguments(pat)
        if u == ℯ
            return Expr(:call, :exp, v)
        end
    elseif (opₛ, opₚ) == (:/, :^)
        u,v = arguments(pat)
        if eq_expr(v, :(-1))
            return Expr(:call, :/, 1, u)
        end
    elseif (opₛ, opₚ) == (:*, :/)
        u, v = arguments(pat)
        return Expr(:call, :*, u, _invert_expr(v))
    end
    return pat
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
            pᵢ′ = :(~$(varname(pᵢ)))
        else
            a, b = arguments(pᵢ)
            pᵢ′ = Expr(:call, :^, a, :(~$(varname(b))))
        end
        # replace in ps′ which may be shorter than ps
        i = findall(==(pᵢ), ps′)
        ps′[i] .= (pᵢ′,)
    end
    return (ps′, σ′)
end

# This handles defslots by
# looping over all combinations of having the
# defslot be a slot variable *or* its default value
# it then combines the resulting matches into θ′′
# except in the case that *no* defaults is used, in which case
# that set of matches is the only one returned
function clear_defslots(ss, p, fₐ, θ)
    #@show :cf, ss, p
    opₚ = operation(p)
    ps = arguments(p)
    inds = findall(has_defslot, ps)

    θ′′ = MatchDict[]
    for inds′ = powerset(1:length(inds))
        ps′, σ′ = set_defslots(ps, opₚ, inds, inds′)
        p′ = pterm(opₚ, ps′)
        θ′ = (merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′))
        # might need to adjust fₐ
        if opₚ == :^ && operation(p′) != :^
            fₐ = nothing
        end
        itr = match_one_to_one(ss, p′, fₐ, θ′)
        (isnothing(itr) || isempty(itr)) && continue
        length(inds′) < length(inds) && return itr # avoid all defslots?
        θ′′ = union(θ′′, itr)
    end

    return θ′′

end
