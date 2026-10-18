## ---- utils.jl (commutative matching) -----

# Utilities used by the commutative matcher (`_ceachmatch`). Those which
# are the same as in the associative-commutative matcher are shared and
# found in ../utils.jl.
#
# MERGE: `merge_vectors_of_matches` has a counterpart, `union_merge`, in ../utils.jl
# which behaves differently; it is marked `MERGE:` with how it differs.

const M = MatchDict
const FAIL_DICT = MatchDict(:_fail, 0)

const NO_MATCH = MatchDict[]
const 𝑀 = Vector{MatchDict}


## matches are ImmutableDicts
# same keys and `isequal` values. (`==` may not return a Bool for
# symbolic values, e.g. SymbolicUtils)
function _isequal_match(σ::MatchDict, σ′::MatchDict)::Bool
    length(σ) == length(σ′) || return false
    for (k, v) ∈ σ
        haskey(σ′, k) || return false
        isequal(v, σ′[k]) || return false
    end
    return true
end

# MERGE: `union_merge` of ../utils.jl returns a generator and has no
# `FAIL_DICT` sentinel; this returns a vector.
function merge_vectors_of_matches(θ::𝑀, σ′::MatchDict)::𝑀
    σ′ === FAIL_DICT && return NO_MATCH
    MatchDict[merge_match(σ, σ′) for σ ∈ θ if iscompatible(σ, σ′)]
end

function merge_vectors_of_matches(θ::𝑀, θ′::𝑀)::𝑀
    [merge_match(σ, σ′) for σ ∈ θ for σ′ ∈ θ′ if iscompatible(σ, σ′)]
end

## AI generated union_merge
function _merge_single(σs::𝑀, σ′::M)::𝑀
    σ′ === FAIL_DICT && return NO_MATCH
    σs == NO_MATCH &&  return NO_MATCH
    merged = MatchDict[]
    sizehint!(merged, length(σs))
    for σ ∈ σs
        iscompatible(σ, σ′) || continue
        push!(merged, merge_match(σ, σ′))
    end
    return isempty(merged) ? MatchDict[] : merged
end

## AI generated union_merge with k=>v
function _merge_single_expr(σs, k, @nospecialize(v))
    σ = match_dict(k => v)
    _merge_single(σs, σ)
end

## co-pilot written utils
function _split_segments(arg_rule)
    seg = Expr[]
    notseg = Any[]
    seg_positions = Int[]
    for (i, pat) ∈ enumerate(arg_rule)
        if is_segment(pat) || is_plus(pat)
            push!(seg, pat)
            push!(seg_positions, i)
        else
            push!(notseg, pat)
        end
    end
    return seg, notseg, seg_positions
end

function _tuple_without_indices(@nospecialize(arg_data), ind, n)
    vals = Any[]
    sizehint!(vals, n - length(ind))
    k = 1
    nextskip = first(ind)
    @inbounds for i ∈ 1:n
        if k <= length(ind) && i == nextskip
            k += 1
            nextskip = k <= length(ind) ? ind[k] : 0
        else
            push!(vals, arg_data[i])
        end
    end
    return tuple(vals...)
end

# Generate every k-tuple of nonnegative integers that sum to n (a
# "composition" of n into k parts, stars-and-bars style), by direct
# recursive construction. This visits exactly the C(n+k-1, k-1) valid
# tuples, as opposed to generating the full (n+1)^k Cartesian product via
# `Iterators.product(0:n, ..., 0:n)` and discarding every tuple whose
# entries don't sum to n -- the latter wastes work that grows quickly
# (exponentially in k) as the number of segment wildcards increases.
function _compositions(n::Int, k::Int)
    k == 1 && return Any[(n,)]
    out = Any[]
    for a ∈ 0:n
        for rest ∈ _compositions(n - a, k - 1)
            push!(out, (a, rest...))
        end
    end
    return out
end


# invert an expr to regularize a/b --> a*b^{-1}
# a rule `u / v` as the factors `u` (unless 1) and `vᵢ^-1` for each factor `vᵢ` of `v`
function _rule_as_powers(rule)
    u, v = arguments(rule)
    vs = _is_operation(*)(v) ? arguments(v) : (v,)
    vs′ = map(_invert_expr, vs)
    u == 1 ? vs′ : Any[u, vs′...]
end
