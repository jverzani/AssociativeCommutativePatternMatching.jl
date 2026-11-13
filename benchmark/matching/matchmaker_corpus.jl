# julia --project=env matchmaker_corpus.jl
# Run MatchMaker.jl's ported test corpora (MatchPy, SymbolicUtils, SymPy,
# Metatheory) through AssociativeCommutativePatternMatching.
#
# Each suite's test helper (`mp`, `mpc`, `sm`) is intercepted: the call's
# pattern, subject, expected matches and variable specs are recorded, and the
# original helper still runs, so MatchMaker's own verdict is kept. Each case is
# then translated to an ACPM Expr pattern and Expr subject (heads declared
# associative/commutative in MatchMaker get the suffixes ₐ/ₘ, which
# `isassociative`/`iscommutative` recognize) and run through `_eachmatch` (AC)
# and `_ceachmatch` (commutative). Their distinct matches are compared with the
# expected ones after normalizing (segment values as argument lists, arguments
# of commutative heads sorted).
using Test, SymbolicUtils, MatchMaker, AssociativeCommutativePatternMatching
using SymbolicUtils: BasicSymbolic, SymReal, Const, iscall, operation, arguments, unwrap_const, issym
const ACPM = AssociativeCommutativePatternMatching
const MM = MatchMaker

# ---- heads: ₐ associative, ₘ commutative
function ACPM.isassociative(x::Symbol)
    x ∈ (:+, :*) && return true
    s = string(x); endswith(s, "ₐ") || endswith(s, "ₐₘ")
end
function ACPM.iscommutative(x::Symbol)
    x ∈ (:+, :*) && return true
    endswith(string(x), "ₘ")
end

# ---- record cases
struct Case
    suite::String
    testset::String
    kind::Symbol            # :maps (expected list of maps) or :count
    pat::Any
    subj::Any
    expected::Any           # Vector of Dicts, or Int
    vars::Dict
    constraints::Vector
    drop::Vector
    mm_pass::Union{Bool,Nothing}
end
const CASES = Case[]
current_testset() = try Test.get_testset().description catch; "" end

function expected_maps(e)
    e === nothing && return Dict[]
    e isa AbstractDict && return [Dict(e)]
    e isa AbstractVector{<:Pair} && return [Dict(e)]
    isempty(e) && return Dict[]
    return [Dict(m) for m in e]
end

const TESTDIR = joinpath(pkgdir(MatchMaker), "test")
const SUITES = [("matchpy", "matchpy/one_to_one.jl"), ("symbolicutils", "su/rewrite.jl"),
                ("sympy", "sympy/match.jl"), ("metatheory", "metatheory/reductions.jl")]

function load_suite(suite, file)
    src = read(joinpath(TESTDIR, file), String)
    for h in ("mp", "mpc", "sm")
        src = replace(src, Regex("function $h\\(") => "function _orig_$h(")
    end
    m = Module(Symbol(suite))
    Core.eval(m, :(using Test, MatchMaker, SymbolicUtils))
    Core.eval(m, :(const _CASES = $CASES; const _Case = $Case; const _SUITE = $suite))
    Core.eval(m, :(const _cts = $current_testset; const _em = $expected_maps))
    # recording wrappers; they return MatchMaker's own verdict
    Core.eval(m, quote
        _VS(v) = Dict{SymbolicUtils.BasicSymbolic{SymbolicUtils.SymReal}, VarSpec.Type}(v...)
        function mp(pat, subj, expected; vars = Dict(), constraints = Constraint[], drop = [])
            ok = try _orig_mp(pat, subj, expected; vars = _VS(vars), constraints = Constraint[constraints...], drop = [drop...]) catch; nothing end
            push!(_CASES, _Case(_SUITE, _cts(), :maps, pat, subj, _em(expected), Dict(vars), collect(constraints), collect(drop), ok))
            something(ok, false)
        end
        function mpc(pat, subj; vars = Dict(), constraints = Constraint[])
            n = try _orig_mpc(pat, subj; vars = _VS(vars), constraints = Constraint[constraints...]) catch; nothing end
            # the expected count is on the other side of `==`; patched below
            push!(_CASES, _Case(_SUITE, _cts(), :count, pat, subj, nothing, Dict(vars), collect(constraints), [], nothing))
            something(n, -1)
        end
        function sm(pat, subj, expected; vars = Dict())
            ok = try _orig_sm(pat, subj, expected; vars = _VS(vars)) catch; nothing end
            push!(_CASES, _Case(_SUITE, _cts(), :maps, pat, subj, _em(expected), Dict(vars), [], [], ok))
            something(ok, false)
        end
    end)
    # `@test mpc(pat, subj) == n`: record n
    src = replace(src, "@test (mpc(pat, subj; vars) >= 1) == want" => "@test _some(mpc(pat, subj; vars), want)")
    src = replace(src, r"@test mpc\((.*?)\) == (\w+)"s => s"@test _count(mpc(\1), \2)")
    Core.eval(m, quote
        function _count(got, n)
            c = _CASES[end]
            _CASES[end] = _Case(c.suite, c.testset, :count, c.pat, c.subj, n, c.vars, c.constraints, c.drop, got == n)
            got == n
        end
    end)
    Core.eval(m, quote
        function _some(got, want)
            c = _CASES[end]
            _CASES[end] = _Case(c.suite, c.testset, :some, c.pat, c.subj, want, c.vars, c.constraints, c.drop, (got >= 1) == want)
            (got >= 1) == want
        end
    end)
    try
        @testset "$suite" begin
            Base.include_string(m, src, file)
        end
    catch err
        @warn "suite $suite raised" err
    end
end

# ---- MatchMaker pattern term → ACPM Expr pattern
struct Untranslatable <: Exception; why::String; end

headsym(op) = begin
    op === (+) && return :+
    op === (*) && return :*
    op isa Function && return nameof(op)
    issym(op) || throw(Untranslatable("head $op"))
    s = string(nameof(op))
    a, c = MM.is_associative(op, Number), MM.is_commutative(op, Number)
    Symbol(s * (a ? "ₐ" : "") * (c ? "ₘ" : ""))
end
identity_of(h) = h === :+ ? 0 : h === :* ? 1 : nothing

leafexpr(t) = begin
    if t isa BasicSymbolic && SymbolicUtils.isconst(t)
        return unwrap_const(t)
    elseif t isa BasicSymbolic && issym(t)
        return nameof(t)
    else
        return t
    end
end

# subject (or expected value) term → Expr
function toexpr(t)
    t isa BasicSymbolic || return t
    iscall(t) || return leafexpr(t)
    Expr(:call, headsym(operation(t)), map(toexpr, arguments(t))...)
end

# the Julia value of an Expr built by `toexpr`, as a SymbolicUtils term
# (for calling MatchMaker predicates from ACPM guards)
const SYMS = Dict{Symbol,Any}()
const HEADS = Dict{Symbol,Any}()
function fromexpr(e)
    e isa Symbol && return SYMS[e]
    e isa Expr || return e
    op = e.args[1]
    f = op === :+ ? (+) : op === :* ? (*) : get(HEADS, op) do
        isdefined(Base, op) ? getfield(Base, op) : error("unknown head $op")
    end
    f(map(fromexpr, e.args[2:end])...)
end
register!(t) = begin
    t isa BasicSymbolic || return
    if issym(t)
        SYMS[nameof(t)] = t
    elseif iscall(t)
        op = operation(t)
        if issym(op)
            HEADS[headsym(op)] = op
        elseif op isa Function
            HEADS[nameof(op)] = op
        end
        foreach(register!, arguments(t))
    end
end


# a MatchMaker predicate takes a term; an ACPM guard gets an Expr, Symbol or number
asterm(v) = v isa BasicSymbolic ? v : v isa Number ? Const{SymReal}(v) : fromexpr(v)
guardfn(p) = v -> (try p(asterm(v)) === true catch; false end)

const MData = MM.MData
isslotspec(s) = MData.isa_variant(s, VarSpec.Slot)

# kinds: var name => (:slot | :segment, enclosing head)
function topat(t, vars, kinds, parent)
    t isa BasicSymbolic || return t
    MM.is_marker_term(t) && return marker(t, vars, kinds, parent)
    iscall(t) || return leafexpr(t)
    op = operation(t)
    if op isa BasicSymbolic && MM.is_marker_term(op)
        F = marker(op, vars, kinds, :head)
        return Expr(:call, F, map(a -> topat(a, vars, kinds, :free), arguments(t))...)
    end
    h = headsym(op)
    Expr(:call, h, map(a -> topat(a, vars, kinds, h), arguments(t))...)
end

function marker(t, vars, kinds, parent)
    v = MM.varsym(t)
    name = nameof(v)
    spec = get(vars, v, nothing)
    op = operation(t)
    if MM.is_segment_marker(op)
        mn, pred = 0, nothing
        if spec !== nothing
            isslotspec(spec) && throw(Untranslatable("segment with slot spec"))
            spec.sequence_predicate === nothing || throw(Untranslatable("sequence predicate"))
            spec.max == typemax(Int) || throw(Untranslatable("segment max"))
            spec.min <= 1 || throw(Untranslatable("segment min > 1"))
            mn, pred = spec.min, spec.predicate
        end
        pred === nothing || throw(Untranslatable("segment element predicate"))
        kinds[name] = (:segment, parent)
        return mn == 0 ? :(~~$name) : :(~~~$name)
    end
    pred, default = nothing, nothing
    if spec !== nothing
        isslotspec(spec) || throw(Untranslatable("slot with segment spec"))
        pred, default = spec.predicate, spec.default
    end
    optional = op === MM.optional
    kinds[name] = (:slot, parent)
    if optional
        default === nothing && throw(Untranslatable("optional without default"))
        d = unwrap_const(default)
        d == identity_of(parent) || throw(Untranslatable("default $d under $parent"))
    end
    core = pred === nothing ? name : Expr(:(::), name, guardfn(pred))
    optional ? :(~!$core) : :(~$core)
end

# ---- normalize a match: var => canonical string
canon(e) = begin
    e isa Expr || return string(e)
    h = e.args[1]
    as = map(canon, e.args[2:end])
    ACPM.iscommutative(h isa Symbol ? h : :_) && sort!(as)
    string(h, "(", join(as, ","), ")")
end
# a value as the matcher gave it → Expr
valexpr(v) = v isa BasicSymbolic ? toexpr(v) : v

segargs_mm(v, h) = begin
    e = valexpr(v)
    if h isa Symbol && identity_of(h) !== nothing
        e == identity_of(h) && return Any[]
        return e isa Expr && e.args[1] == h ? e.args[2:end] : Any[e]
    end
    e isa Expr && return e.args[2:end] # op(captured…)
    Any[]
end
function normalize(σ, kinds, drop; mm::Bool)
    ps = String[]
    for (k, v) in σ
        k = k isa Symbol ? k : nameof(k)
        (k in (:____, :MATCH, :_fail) || k in drop) && continue
        kind, h = get(kinds, k, (:slot, :free))
        s = if kind == :segment
            xs = mm ? segargs_mm(v, h) : collect(Any, v isa Union{Tuple,AbstractVector} ? v : (v,))
            cs = map(canon ∘ valexpr, xs)
            h isa Symbol && ACPM.iscommutative(h) && sort!(cs)
            "[" * join(cs, ",") * "]"
        else
            canon(valexpr(v))
        end
        push!(ps, "$k => $s")
    end
    join(sort!(ps), "; ")
end

collectvars!(acc, t) = (t isa BasicSymbolic || return acc;
    MM.is_marker_term(t) ? push!(acc, MM.varsym(t)) : iscall(t) ? (collectvars!(acc, operation(t)); foreach(a -> collectvars!(acc, a), arguments(t))) : nothing; acc)

# ---- time per call, µs: best of three batches of ≥ 1 ms
function timeit(f)
    f(); n = 1; t = 0.0
    while true
        t = @elapsed for _ in 1:n; f(); end
        (t > 1e-3 || n >= 2^14) && break
        n *= 2
    end
    best = t / n
    for _ in 1:2
        tᵢ = @elapsed for _ in 1:n; f(); end; best = min(best, tᵢ / n)
    end
    best * 1e6
end

verdict(c, got, want) = c.kind == :count ? length(got) == want : c.kind == :some ? (!isempty(got)) == want : got == want
const CAP = 5000
ac_all(p, s) = collect(Iterators.take(ACPM._eachmatch(p, s), CAP))
c_all(p, s) = ACPM._ceachmatch(p, s)

function run_case(c::Case)
    r = Dict{String,Any}("suite" => c.suite, "testset" => c.testset, "mm_pass" => c.mm_pass)
    register!(c.pat); register!(c.subj)
    kinds = Dict{Symbol,Any}()
    drop = Set(nameof.(c.drop))
    c.kind == :count && c.expected === nothing && (r["untranslatable"] = "expected count not recorded"; return r)
    try
        isempty(c.constraints) || throw(Untranslatable("cross-variable constraint"))
        r["pattern"] = topat(c.pat, c.vars, kinds, :free)
        r["subject"] = toexpr(c.subj)
    catch err
        r["untranslatable"] = err isa Untranslatable ? err.why : first(sprint(showerror, err), 120)
        r["pattern_mm"] = string(c.pat); r["subject_mm"] = string(c.subj)
        return r
    end
    p, s = r["pattern"], r["subject"]
    want = c.kind in (:count, :some) ? c.expected : Set(normalize(σ, kinds, drop; mm = true) for σ in c.expected)
    # MatchMaker itself, timed on its own terms
    # the suites share one spec table; keep the variables in this pattern
    pvars = Set{Any}(); collectvars!(pvars, c.pat)
    vs = Dict{BasicSymbolic{SymReal},VarSpec.Type}(k => v for (k, v) in c.vars if any(isequal(k), pvars))
    try
        m = compile_pattern(c.pat; vars = vs)
        r["t_mm"] = timeit(() -> matchall(m, c.subj; constraints = Constraint[c.constraints...]))
        got = Set(normalize(σ, kinds, drop; mm = true) for σ in matchall(m, c.subj; constraints = Constraint[c.constraints...]))
        r["mm_ok"] = verdict(c, got, want)
    catch err
        r["mm_error"] = first(sprint(showerror, err), 200)
    end
    for (key, f, prep) in (("ac", ac_all, identity), ("c", c_all, identity), ("cc", c_all, ACPM.compile_pattern))
        try
            q = prep(p)
            σs = f(q, s)
            got = Set(normalize(σ, kinds, drop; mm = false) for σ in σs)
            r[key * "_ok"] = verdict(c, got, want)
            r[key * "_got"] = collect(got)[1:min(end, 6)]
            r["t_" * key] = timeit(() -> f(q, s))
        catch err
            r[key * "_error"] = first(sprint(showerror, err), 200)
            r[key * "_ok"] = false
        end
    end
    r["want"] = c.kind in (:count, :some) ? want : collect(want)[1:min(end, 6)]
    r
end

for (suite, file) in SUITES
    load_suite(suite, file)
end
@info "recorded $(length(CASES)) cases"
const RESULTS = map(run_case, CASES)

# ---- report
using Statistics
gm(v) = isempty(v) ? NaN : exp(mean(log.(v)))
r2(x) = round(x, digits = 2)
# guards are spliced-in functions; print them as `pred`
showpat(e) = string(_showpat(e))
_showpat(e) = e isa Expr ? (e.head == :(::) && !(e.args[2] isa Symbol) ? Expr(:(::), e.args[1], :pred) : Expr(e.head, map(_showpat, e.args)...)) : e
io = IOBuffer()
println(io, "MatchMaker $(pkgversion(MatchMaker)) test corpora through AssociativeCommutativePatternMatching $(pkgversion(ACPM))")
println(io, "ok = same set of distinct matches as MatchMaker's expected answer (or same count / same yes-no)\n")
println(io, rpad("suite", 14), lpad("cases", 6), lpad("transl.", 8), lpad("mm ok", 7), lpad("ac ok", 7), lpad("c ok", 7),
        lpad("med mm", 8), lpad("med ac", 8), lpad("med cc", 8), lpad("ac/mm", 7), lpad("cc/mm", 7))
for suite in [unique(r["suite"] for r in RESULTS); "all"]
    rs = filter(r -> suite == "all" || r["suite"] == suite, RESULTS)
    tr = filter(r -> !haskey(r, "untranslatable"), rs)
    tt = filter(r -> all(haskey(r, k) for k in ("t_mm", "t_ac", "t_cc")), tr)
    tm, ta, tc = [r["t_mm"] for r in tt], [r["t_ac"] for r in tt], [r["t_cc"] for r in tt]
    println(io, rpad(suite, 14), lpad(length(rs), 6), lpad(length(tr), 8),
        lpad(count(r -> get(r, "mm_ok", false), tr), 7), lpad(count(r -> r["ac_ok"], tr), 7), lpad(count(r -> r["c_ok"], tr), 7),
        lpad(r2(median(tm)), 8), lpad(r2(median(ta)), 8), lpad(r2(median(tc)), 8), lpad(r2(gm(ta ./ tm)), 7), lpad(r2(gm(tc ./ tm)), 7))
end
println(io, "\ntimes: µs per call for all matches; mm = matchall (subject DAG built per call), ac = _eachmatch, cc = _ceachmatch compiled;")
println(io, "ACPM runs on Expr subjects here. ac/mm, cc/mm are geometric means of the per-case ratios.\n")
println(io, "Not translated:")
why = Dict{String,Int}()
for r in RESULTS
    haskey(r, "untranslatable") && (k = r["suite"] * ": " * r["untranslatable"]; why[k] = get(why, k, 0) + 1)
end
foreach(((k, n),) -> println(io, "  ", n, "  ", k), sort(collect(why), by = last, rev = true))
for key in ("ac", "c")
    println(io, "\nFailures of ", key == "ac" ? "_eachmatch" : "_ceachmatch", ":")
    for r in RESULTS
        haskey(r, "untranslatable") && continue
        r[key * "_ok"] && continue
        println(io, "  ", r["suite"], " [", r["testset"], "]  ", showpat(r["pattern"]), "  ~  ", r["subject"])
        println(io, "      want ", r["want"])
        println(io, "      got  ", get(r, key * "_got", first(get(r, key * "_error", ""), 100)))
    end
end
report = String(take!(io))
print(report)
mkpath(joinpath(@__DIR__, "results"))
write(joinpath(@__DIR__, "results", "matchmaker_corpus.txt"), report)
