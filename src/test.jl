# Import package and any files here ↴
include("Muffins.jl")

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

    for method in split(methods, ",")
        res = 0

        if method == "FC"
            res = Muffins.fc(m, s, output = 0)
        end

        if method == "HALF"
            res = Muffins.half(m, s, output = 0)
        end

        if method == "INT"
            res = Muffins.int(m, s, output = 0)
        end

        if method == "MID"
            res = Muffins.mid(m, s, output = 0)
        end

        if startswith(method, "EBM")
            res = Muffins.ebm(m, s, output = 0)
        end

        if startswith(method, "HBM")
            res = Muffins.hbm(m, s, output = 0)
        end

        if method == "GAP"
            res = Muffins.gap(m, s, output = 0)
        end

        if res != 0
            if res != num // den
                append!(incorrect, [[(m, s), method, res, alpha]])
            end
        else
            append!(skipped, [[(m, s), method]])
        end
    end

    if Muffins.muffins(m, s, output = 0) != num // den
        append!(nosol, [(m, s)])
    end

end

# Customize output here ↴
for x in nosol
    println(x)
end
for x in incorrect
    if x[3] != 1
        println(x)
    end
end