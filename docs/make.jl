using Documenter, AssociativeCommutativePatternMatching

makedocs(sitename="AssociativeCommutativePatternMatching Documentation",
         repo = "github.com/jverzani/AssociativeCommutativePatternMatching.jl.git",
         pages = [
             "Home" => "index.md",
             "Commutative matching" => "commutative.md",
             "Commutative patterns" => "commutative_patterns.md",
             "Reference" => "reference.md",
         ],
         format = Documenter.HTML(
             prettyurls = get(ENV, "CI", nothing) == "true"
         )
         )

# Documenter can also automatically deploy documentation to gh-pages.
# See "Hosting Documentation" and deploydocs() in the Documenter manual
# for more information.
deploydocs(
    repo = "github.com/jverzani/AssociativeCommutativePatternMatching.jl.git"
)
