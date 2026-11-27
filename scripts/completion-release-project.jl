using Pkg

# Versions exercised in the audit. Installing sources here is only for CI;
# Fatou must not run packages or manage the user's environment at runtime.
Pkg.add([
    PackageSpec(name="CSV", version=v"1.3.0"),
    PackageSpec(name="DataFrames", version=v"1.8.3"),
    PackageSpec(name="DataFramesMeta", version=v"0.15.7"),
    PackageSpec(name="DataStructures", version=v"0.19.7"),
    PackageSpec(name="Distributions", version=v"0.25.135"),
    PackageSpec(name="HTTP", version=v"1.11.1"),
    PackageSpec(name="NearestNeighbors", version=v"0.4.29"),
    PackageSpec(name="Pluto", version=v"1.1.0"),
    PackageSpec(name="StaticArrays", version=v"1.9.25"),
    PackageSpec(name="StatsBase", version=v"0.34.14"),
])
