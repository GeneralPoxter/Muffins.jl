# Import package and any files here ↴
include("FC.jl")
using .FC

include("Half.jl")
using .Half

include("Int.jl")
using .Int

include("Mid.jl")
using .Mid

include("EBM.jl")
using .EBM

include("HBM.jl")
using .HBM

# Make sure test.txt is in the same folder as test.jl
lines = open("test.txt") do file
    readlines(file)
end

# Array of failed cases: [(muffins, students), method, generated answer, actual answer]
incorrect = []

# Array of cases with no solutions over all methods: (muffins, students)
nosol = []

# Array of skipped cases: [(muffins, students), method]
skipped = []

for case in lines
    println(case)
    (m, s, methods, alpha) = tuple(split(case, " ")...)

    m = parse(Int64, m)
    s = parse(Int64, s)

    alphaF = split(alpha, "/")
    num = parse(Int64, alphaF[1])
    den = parse(Int64, alphaF[2])

    tested = 0
    correct = 0
    for method in split(methods, ",")
        # For each method you want to test below:
        # Uncomment "# res = METHOD(m, s)" and replace METHOD with the proper function name

        res = 0

        if method == "FC"
            res = fc(m, s, output=0)
        end

        if method == "HALF"
            res = half(m, s, output=0)
        end

        if method == "INT"
            res = int(m, s, output=0)
        end

        if method == "MID"
            res = mid(m, s, output=0)
        end

        if startswith(method, "EBM")
            res = ebm(m, s, output=0)
        end

        if startswith(method, "HBM")
            res = hbm(m, s, output=0)
        end

        if startswith(method, "GAP")
            # res = METHOD(m, s)
        end
        
        if res != 0
            tested += 1
            if res != num//den
                append!(incorrect, [[(m, s), method, res, alpha]])
            else
                correct += 1
            end
        else
            append!(skipped, [[(m, s), method]])
        end
    end

    if tested != 0 && correct == 0
        append!(nosol, [(m, s)])
    end

end

# Customize output here ↴