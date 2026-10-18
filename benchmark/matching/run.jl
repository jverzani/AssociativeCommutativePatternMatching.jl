# julia --project=env run.jl
# Matches each pattern of cases.jl against its subject, a SymbolicUtils term,
# with four matchers, and writes results/matching.json (read by build.jl):
#   ac  AssociativeCommutativePatternMatching._eachmatch (all matches, lazily)
#   c   AssociativeCommutativePatternMatching._ceachmatch (a vector of matches)
#   su  SymbolicUtils @rule; all matches are found by a continuation that
#       records the bindings and returns `nothing`, so the matcher backtracks
#   si  SymbolicIntegration's rule2.jl, `check_expr_r`, which returns one match
const T_START = time()
using SymbolicUtils, SymbolicIntegration, AssociativeCommutativePatternMatching
const ACPM = AssociativeCommutativePatternMatching
const SI = SymbolicIntegration

# SymbolicUtils v4 wraps numbers as constants; the glue the tests use
ACPM.unwrap_const(x::SymbolicUtils.BasicSymbolic) = SymbolicUtils.unwrap_const(x)

const HERE = @__DIR__
const CASES = include(joinpath(HERE, "cases.jl"))
const CAP = 5000 # stop collecting matches after this many

@syms x y z a b c t
const VARS = Dict(:x => x, :y => y, :z => z, :a => a, :b => b, :c => c, :t => t)
const VALS = Dict(x => 0.37, y => 0.59, z => 0.71, a => 1.13, b => 1.29, c => 1.47, t => 0.83)

function build(ex)
    m = Module()
    for (k, v) in VARS
        Core.eval(m, :(const $k = $v))
    end
    Core.eval(m, ex)
end

# ---- a match as sorted pairs; segments as vectors; sentinels dropped
function normal(σ)
    ps = Pair{Symbol,Any}[]
    for (k, v) in σ
        k in (:____, :MATCH, :_fail) && continue
        v = isa(v, Union{Tuple, AbstractVector}) ? collect(Any, v) : v
        push!(ps, k => v)
    end
    sort!(ps, by = first)
end

# ---- the four matchers: (all matches, first match)
first_or_nothing(itr) = (for σ in itr; return σ; end; nothing)

ac_all(p, s) = collect(Iterators.take(ACPM._eachmatch(p, s), CAP))
ac_first(p, s) = ACPM._match(p, s)
c_all(p, s) = ACPM._ceachmatch(p, s)
c_first(p, s) = ACPM._cmatch(p, s)

const SU_RULES = Dict{Expr,Any}()
su_rule(p) = get!(() -> Core.eval(Main, :(SymbolicUtils.@rule $p => true)), SU_RULES, p)
# as `(r::Rule)(term)` does, zero the meter of commutative backtracking, which
# falls back to the first match once over SymbolicUtils.COMM_BACKTRACK_BUDGET
su_reset() = (SymbolicUtils.COMM_BT_USED[][] = 0)
function su_all(p, s)
    found = Any[]
    su_reset()
    su_rule(p).matcher((bs, n) -> (n == 1 && length(found) < CAP && push!(found, bs); nothing),
                       (s,), SymbolicUtils.EMPTY_IMMUTABLE_DICT)
    found
end
su_first(p, s) = (su_reset(); su_rule(p).matcher((bs, n) -> n == 1 ? bs : nothing, (s,), SymbolicUtils.EMPTY_IMMUTABLE_DICT))

function si_first(p, s)
    σ = SI.check_expr_r(s, p, SI.MatchDict())
    σ === SI.FAIL_DICT ? nothing : σ
end
si_all(p, s) = (σ = si_first(p, s); σ === nothing ? Any[] : Any[σ])

const METHODS = [("ac", ac_all, ac_first), ("c", c_all, c_first), ("su", su_all, su_first), ("si", si_all, si_first)]

# ---- verify a match: put it into the pattern and compare numerically
struct Splat; vs::Vector{Any}; end
name(p) = (q = p.args[2]; q isa Expr && q.head == :(::) ? name(Expr(:call, :~, q.args[1])) :
           q isa Expr && q.args[1] in (:~, :!) ? name(q) : q)
isslotexpr(p) = p isa Expr && p.head == :call && p.args[1] == :~ && length(p.args) == 2
issegexpr(p) = isslotexpr(p) && (q = p.args[2]; q isa Expr && q.head == :call && q.args[1] == :~)
const EMPTY = Dict(:+ => 0, :* => 1)
function instantiate(p, σ)
    p isa Symbol && return p == :ℯ ? ℯ : VARS[p]
    p isa Expr || return p
    if isslotexpr(p)
        v = σ[name(p)]
        return issegexpr(p) ? Splat(isa(v, Vector) ? v : Any[v]) : v
    end
    op = p.args[1]
    f = isslotexpr(op) ? σ[name(op)] : getfield(Base, op)
    args = Any[]
    for q in p.args[2:end]
        v = instantiate(q, σ)
        v isa Splat ? append!(args, v.vs) : push!(args, v)
    end
    isempty(args) && return EMPTY[op]
    length(args) == 1 && op in (:+, :*) && return only(args)
    f(args...)
end
function numval(ex)
    ex isa SymbolicUtils.BasicSymbolic || return float(ex)
    v = SymbolicUtils.unwrap_const(SymbolicUtils.substitute(ex, VALS; fold = Val(true)))
    isa(v, Number) ? float(v) : nothing
end
function verify(p, s, σ)
    try
        d = Dict(normal(σ))
        u, v = numval(instantiate(p, d)), numval(s)
        (u === nothing || v === nothing) && return "unchecked"
        abs(u - v) <= 1e-8 * max(1, abs(v)) ? "ok" : "wrong"
    catch
        "unchecked"
    end
end

# ---- time per call, in microseconds: best of three batches of ≥ 2 ms
function timeit(f)
    f()
    n, t = 1, 0.0
    while true
        t = @elapsed for _ in 1:n
            f()
        end
        (t > 2e-3 || n >= 2^16) && break
        n *= 2
    end
    best = t / n
    for _ in 1:2
        tᵢ = @elapsed for _ in 1:n
            f()
        end
        best = min(best, tᵢ / n)
    end
    round(best * 1e6, sigdigits = 3)
end

# ---- a small JSON writer
json(::Nothing) = "null"
json(x::Bool) = string(x)
json(x::Real) = isfinite(x) ? string(x) : "null"
function json(s::AbstractString)
    io = IOBuffer(); print(io, '"')
    for ch in s
        ch == '"' ? print(io, "\\\"") : ch == '\\' ? print(io, "\\\\") :
        ch == '<' ? print(io, "\\u003c") : ch < ' ' ? print(io, "\\u", string(UInt16(ch), base = 16, pad = 4)) : print(io, ch)
    end
    print(io, '"'); String(take!(io))
end
json(v::AbstractVector) = "[" * join(json.(v), ",") * "]"
json(d::AbstractDict) = "{" * join((json(string(k)) * ":" * json(v) for (k, v) in d), ",") * "}"

showval(v::Vector) = "[" * join(string.(v), ", ") * "]"
showval(v) = string(v)
showmatch(ps) = isempty(ps) ? "(empty)" : join(("$k => $(showval(v))" for (k, v) in ps), ", ")

const T_LOADED = time()
results = map(enumerate(CASES)) do (i, (group, pat, subex, note))
    s = build(subex)
    @info "case $i: $pat ~ $s"
    row = Dict{String,Any}("i" => i, "group" => group, "pattern" => string(pat), "subject" => string(subex),
                           "stored" => string(s), "note" => note)
    for (key, all, first1) in METHODS
        r = Dict{String,Any}()
        try # the first match, as a rule would use it
            σ1 = first1(pat, s)
            r["first"] = σ1 === nothing ? nothing : showmatch(normal(σ1))
            r["t_first"] = timeit(() -> first1(pat, s))
        catch err
            r["error"] = first(sprint(showerror, err), 300)
        end
        try # every match
            σs = all(pat, s)
            ns = unique(normal.(σs))
            checks = [verify(pat, s, σ) for σ in Iterators.take(σs, 200)]
            r["total"] = length(σs)
            r["capped"] = length(σs) >= CAP
            r["distinct"] = length(ns)
            r["matches"] = [showmatch(n) for n in Iterators.take(ns, 40)]
            r["wrong"] = count(==("wrong"), checks)
            r["unchecked"] = count(==("unchecked"), checks)
            r["t_all"] = key == "si" ? get(r, "t_first", nothing) : timeit(() -> all(pat, s))
        catch err
            r["error_all"] = first(sprint(showerror, err), 300)
        end
        row[key] = r
    end
    row
end

versions = Dict("Julia" => string(VERSION))
for (k, m) in Base.loaded_modules
    k.name in ("AssociativeCommutativePatternMatching", "SymbolicUtils", "SymbolicIntegration") || continue
    versions[k.name] = string(pkgversion(m))
end
commit = try
    c = readchomp(`git -C $HERE rev-parse --short HEAD`)
    dirty = readchomp(`git -C $HERE status --porcelain --untracked-files=no -- ../../src`)
    c * (isempty(dirty) ? "" : " (with uncommitted changes)")
catch
    "unknown"
end
data = Dict("cases" => results, "versions" => versions, "commit" => commit,
            "date" => Libc.strftime("%Y-%m-%d", time()), "cap" => CAP,
            "load" => round(T_LOADED - T_START, digits = 1), "wall" => round(time() - T_START, digits = 1))
mkpath(joinpath(HERE, "results"))
write(joinpath(HERE, "results", "matching.json"), json(data))
@info "wrote results/matching.json in $(round(time() - T_START, digits = 1)) s"
