# julia build.jl
# Builds results/matching_comparison.html from results/matching.json and template.html
const HERE = @__DIR__
data = read(joinpath(HERE, "results", "matching.json"), String)
html = replace(read(joinpath(HERE, "template.html"), String), "/*DATA*/null" => data)
write(joinpath(HERE, "results", "matching_comparison.html"), html)
println("wrote results/matching_comparison.html")
