using Documenter, AssociativeCommutativePatternMatching
using MaterialDocs

makedocs(sitename="AssociativeCommutativePatternMatching Documentation",
         repo = "github.com/jverzani/AssociativeCommutativePatternMatching.jl.git",
         pages = [
             "Home" => "index.md",
             "The two matchers" => "matchers.md",
             "Reference" => "reference.md",
         ],
         format = Material3(;
             theme = :ocean_depth,
             dark_mode = :toggle,
             canonical = "https://jverzani.github.io/AssociativeCommutativePatternMatching.jl",
             edit_link = "main",
             assets = String[],
         )
         )

# Documenter can also automatically deploy documentation to gh-pages.
# See "Hosting Documentation" and deploydocs() in the Documenter manual
# for more information.
deploydocs(
    repo = "github.com/jverzani/AssociativeCommutativePatternMatching.jl.git"
)
