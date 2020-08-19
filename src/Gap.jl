module Gap

using JuMP
using Cbc

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

include("FC.jl")
using .FC

include("Half.jl")
using .Half

export gap, vgap

# Determines upper bound alpha with the Gap Method
# Author: Jason Liu
function gap(m::Int64, s::Int64; output::Int64=2)
    output > 0 && printHeader(center("GAP METHOD"))

    if m < s
        if output > 0
            printf("Gap Method does not apply", line=true)
            printEnd()
        end
        return 1
    elseif m % s == 0
        if output > 0
            printfT("Gap Method",
                    "Since $m % $s = 0, muffins($m,$s) = 1")
            printEnd()
        end
        return 1
    end

    # Compute alpha candidates
    alphas = []
    upper = min(fc(m, s, output=0), half(m, s, output=0))
    for b=1:m
        for n=Int64(ceil(b*s/3)):Int64(floor(b*s*upper))
            append!(alphas, n//(b*s))
        end
    end
    append!(alphas, 1//3)
    alphas = sort(unique(alphas))

    # Test alpha candidates with binary search
    potAlphas = []
    (left, right) = (1, length(alphas))
    while left <= right
        mid = Int64(floor((left+right)/2))
        append!(potAlphas, alphas[mid])
        if vgap(m, s, alphas[mid], output=0)
            right = mid - 1
        else
            left = mid + 1
        end
    end

    for alpha in reverse(potAlphas)
        if vgap(m, s, alpha, output=0)
            vgap(m, s, alpha, output=output)
            return alpha
        end
    end

    if output > 0
        printf("All α candidates were inconclusive, Gap Method inconclusive", line=true)
        printEnd()
    end
    1
end

# Helper function for gap -- verifies whether gap(m, s, alpha) is conclusive
function vgap(m::Int64, s::Int64, alpha::Rational{Int64}; output::Int64=2)
    if m < s || m % s == 0
        output > 0 && printf("VGap does not apply", line=true)
        false
    elseif alpha < 1/3
        output > 0 && printfT("No piece size < 1/3", "For m ≥ s, α must be ≥ 1/3")
        false
    elseif alpha > 1
        output > 0 && printfT("No piece size > 1", "α must be ≤ 1")
        false
    else
        (V, W, sV, sW) = sv(m, s)
        numV = (V)sV
        numW = (W)sW

        # Initialize Gap Method proof
        if output > 1
            # Define and format variables for proof
            alphaF = formatFrac(alpha)
            size = formatFrac(m//s)
            a = formatFrac(m//(V+1)s)
            b = max(1-m//(W-1)s, 0)
            b1 = formatFrac(1-b)
            b = formatFrac(b)

            # Establish assumptions and premises
            printHeader("CLAIM")
            printfT("Claim",
                    "For all ($m, $s) procedures where $s students each receive $size muffins, the smallest piece size is bounded above by α = $alphaF",
                    "Proven by contradicting the assumption")

            printHeader("ASSUMPTION")
            printfT("Assumption",
                    "Assume muffins($m,$s) > α ≥ 1/3")
            printfT("Property of Buddies",
                    "Since muffins($m,$s) > 1/3, each muffin must be cut into 2 shs, totaling $(2m) shs",
                    "",
                    "Since each muffin is cut into 2 shs that are buddies, each sh of size x must imply the existence of a sh of size 1-x")

            # Begin casework
            printHeader("CASEWORK")

            printfT("Case 1",
            "Alice has ≥ $(V+1) shs",
            "One of them is ≤ ($size × 1/$(V+1)) = $a",
            "",
            "Contradicts assumption if α ≥ $a")

            if W-1 <= 1 && m/s > 1
                printfT("Case 2",
                        "Bob cannot have ≤ $(W-1) shs since $size > 1, so this case is impossible")
            else
                printfT("Case 2",
                        "Bob has ≤ $(W-1) shs",
                        "One of them is ≥ ($size × 1/$(W-1)) = $b1",
                        "Its buddy is ≤ (1 - $b1) = $b",
                        "",
                        "Contradicts assumption if α ≥ $b")
            end
        end

        # Check if V-Conjecture applies
        if m//s * 1//(V+1) > alpha || 1 - m//s * 1//(W-1) > alpha
            output > 0 && printf("V-Conjecture does not apply, VGap failed", line=true)
            return false
        end

        ((_, x), (y, _)) = findend(m, s, alpha, V)
        xOriginal = m//s - alpha*(V-1)
        yOriginal = m//s - (1-alpha)*(V-2)

        # Check if FindEnd works
        if x != xOriginal && y != yOriginal
            output > 0 && printf("FindEnd inconclusive, VGap failed", line=true)
            return false
        end

        # Define and format variables for proof
        cd = lcm(s, denominator(x), denominator(y), 2)
        alphaF = formatFrac(alpha, cd)
        alpha1 = formatFrac(1-alpha, cd)
        size = formatFrac(m//s)
        a = formatFrac(m//s-x, cd)
        b = formatFrac(m//s-y, cd)
        xF = formatFrac(x, cd)
        x1 = formatFrac(1-x, cd)
        yF = formatFrac(y, cd)
        y1 = formatFrac(1-y, cd)
        diff = abs(numV-numW)

        # Continue proof
        if output > 1
            # Continue casework
            printfT("Note",
                    "The only cases that need to be considered deal with everyone having either $W or $V shs, so:",
                    "",
                    "$(W)·s_$W + $(V)·s_$V = $(2m)  (total shs)",
                    "s_$W + s_$V = $s  (total students)",
                    "where s_N = # of students with N shs",
                    "",
                    "The solution to the system is:",
                    "s_$W = $sW, s_$V = $sV",
                    "So there are $numW $W-shs and $numV $V-shs")

            if x == xOriginal
                printfT("Case 3",
                        "Alice has a $V-sh ≥ $xF",
                        "Her other $(V-1) $V-shs sum to ≤ ($size - $xF) = $a",
                        "One of them is ≤ ($a × 1/$(V-1)) = $alphaF",
                        "",
                        "Contradicts assumption if α ≥ $alphaF")
            else
                printfT("Case 3",
                        "FindEnd did not produce a conclusive bound for $V-shs")
            end

            if y == yOriginal
                printfT("Case 4",
                        "Bob has a $W-sh ≤ $yF",
                        "His other $(W-1) $W-shs sum to ≥ ($size - $yF) = $b",
                        "One of them is ≥ ($b × 1/$(W-1)) = $alpha1",
                        "Its buddy is ≤ (1 - $alpha1) = $alphaF",
                        "",
                        "Contradicts assumption if α ≥ $alphaF")
            else
                printfT("Case 4",
                        "FindEnd did not produce a conclusive bound for $W-shs")
            end

            printHeader("CASE 5: INTERVAL ANALYSIS")
            println()
            printf("The following intervals capture the negation of the previous cases:")
            if alpha < x <= y < 1-alpha
                println("\n",
                        interval(["(", alphaF],
                                [")[", xF],
                                ["](", yF],
                                [")", alpha1],
                                labels=["$numV $V-shs", "0", "$numW $W-shs"]))
                printLine()
            else
                if xF != alphaF
                    println("\n",
                            interval(["(", alphaF],
                                    [")[", xF],
                                    [")", alpha1],
                                    labels=["$numV $V-shs", "0 $V-shs"]))
                else
                    println("\n",
                            "No negation interval for $V-shs")
                end

                if yF != alpha1
                    println("\n",
                            interval(["(", alphaF],
                                    ["](", yF],
                                    [")", alpha1],
                                    labels=["0 $W-shs", "$numW $W-shs"]))
                else
                    println("\n",
                            "No negation interval for $W-shs")
                end

                printfT("Case 5",
                        "The Gap Method is inconclusive on these intervals, VGap failed")
            end
        end

        # Fail if interval inconclusive
        if x > y || x == alpha || y == 1-alpha
            output == 1 && printf("Could not generate disjoint intervals, VGap failed", line=true)
            return false
        end

        # Define and format variables for proof
        (vMin, vMax, sMin, sMax) = (V, W, sV, sW)
        (i, j, k, l) = (xF, yF, y1, x1)
        (rngMin, rngMax, rngS, rngL) = ((alphaF, xF), (x1, alpha1), (yF, y1), (x1, alpha1))
        if numV > numW
            (vMin, vMax, sMin, sMax) = (W, V, sW, sV)
            (i, j, k, l) = (y1, x1, xF, yF)
            (rngMin, rngMax, rngS, rngL) = ((yF, alpha1), (alphaF, yF), (alphaF, y1), (x1, xF))
        end
        numMin = (vMin)sMin

        # Conclude interval case with case by case analysis
        if output > 1
            printfT("Property of Buddies",
                    "Because 0 shs lie in [$xF,$yF], 0 shs must also lie in [$y1,$x1]",
                    "",
                    "Similary, the $numMin $vMin-shs in ($(rngMin[1]),$(rngMin[2])) implies $numMin $vMax-shs in ($(rngMax[1]),$(rngMax[2]))")
            println()
            printf("The following intervals capture the previous statements:")
            println("\n",
                    interval(["(", alphaF],
                            [")[", i],
                            ["](", j],
                            [")[", k],
                            ["](", l],
                            [")", alpha1],
                            labels=["$numMin $V-shs", "0", "$diff $vMax-shs", "0", "$numMin $W-shs"]))
            printLine()

            printfT("Note",
                    "Let the $vMax-shs that lie in ($(rngS[1]),$(rngS[2])) be small $vMax-shs",
                    "Let the $vMax-shs that lie in ($(rngL[1]),$(rngL[2])) be large $vMax-shs")
        end

        # Determine possible small-sh, large-sh combinations
        posCombo = []
        for k=0:vMax
            upperB = (vMax-k)*toFrac(rngL[2]) + (k)*toFrac(rngS[2])
            lowerB = (vMax-k)*toFrac(rngL[1]) + (k)*toFrac(rngS[1])
            if upperB > m//s > lowerB
                append!(posCombo, k)
            end
        end

        # Diverge from Interval Method
        if length(posCombo) > 0
            mid = formatFrac(1//2, cd)
            if output > 1
                combos = ["$k small $vMax-shs and $(vMax-k) large $vMax-shs" for k in posCombo]
                printfT("Case 5",
                        "All combinations of small and large $vMax-shs are impossible except for:",
                        "",
                        combos...,
                        "",
                        "because the range of muffin amounts for the others does not include $size")

                printHeader("CASE 5: MIDPOINT ANALYSIS")
                printfT("Property of Buddies",
                        "The # of $vMax-shs in ($j, $mid) is equal to the # of $vMax-shs in ($mid, $k)")
            end

            bounds = [[toFrac(j), 1//2], [1//2, toFrac(k)], [toFrac(l), toFrac(alpha1)]]
            smallBounds = [toFrac(j), toFrac(k)]
            solid = [toFrac(l), toFrac(alpha1)]
            intervals = [["(", j], ["|", mid], [")[", k], ["](", l], [")", alpha1]]
            labels = ["z $W-shs", "z $W-shs", "0", "$numV $W-shs"]
            intervalDefs = ["A = ($j,$mid)", "B = ($mid,$k) (|A| = |B| = z)", "C = ($l,$alpha1) (|C| = $numV)"]
            if numW < numV
                bounds = [[alpha, toFrac(i)], [toFrac(j), 1//2], [1//2, toFrac(k)]]
                smallBounds = [alpha, toFrac(i)]
                solid = [alpha, toFrac(i)]
                intervals = [["(", alphaF], [")[", i], ["](", j], ["|", mid], [")", k]]
                labels = ["$numW $V-shs", "0", "z $V-shs", "z $V-shs"]
                intervalDefs = ["A = ($alphaF, $i) (|A| = $numW)", "B = ($j, $mid)", "C = ($mid, $k) (|B| = |C| = z)"]
            end

            if output > 1
                println()
                printf("The following intervals capture what we know about the $V-shs:")
                println("\n",
                interval(intervals...,
                        labels=labels))
                printLine()
                printfT("Note",
                        "We define the following intervals:",
                        intervalDefs...)
            end

            # Determine possible interval combinations
            posInt = intCombo(m, s, vMax, bounds, smallBounds, posCombo)

            if length(posInt) > 0
                if output > 1
                    printfT("Note",
                            "Let the notation (a, b, c, ...) denote a combination of $vMax-shs where there are:",
                            "a shs in interval A",
                            "b shs in interval B",
                            "c shs in interval C",
                            "...",
                            "",
                            "A (a, b, c, ...)-student denotes a student with that combination of $vMax-shs")
                    printfT("Midpoint Analysis I",
                            "Given the possible small and large $vMax-sh combinations,",
                            "all combinations of $vMax-shs from intervals A, B, and C are impossible except for:",
                            "",
                            posInt...,
                            "",
                            "because the range of muffin amounts for the others does not include $size")
                end

                # Check if posInt is too large
                if length(posInt) > 5
                    output > 1 && printf("The # of possible interval combinations is too large, skipping Midpoint Analysis", line=true)
                    solution = [0, 0]
                else
                    # Set up and solve system of equations
                    iter = 1:length(posInt)
                    (a, b, c) = (getindex.(posInt, 1), getindex.(posInt, 2), getindex.(posInt, 3))
                    (A, B, C) = ("A", "B", "C")
                    if numW < numV
                        (a, b, c) = (b, c, a)
                        (A, B, C) = (B, C, A)
                    end

                    equations = [
                        join(["$(a[i])·x_$i" for i=iter], " + ") * " = " * join(["$(b[i])·x_$i" for i=iter], " + "),
                        join(["$(c[i])·x_$i" for i=iter], " + ") * " = |$C| = $numMin",
                        join(["x_$i" for i=iter], " + ") * " = s_$vMax = $sMax",
                        "",
                        ["where x_$i is the # of $(posInt[i])-students" for i=iter]...
                    ]

                    # Test all possible non-negative integer solutions with system
                    model = Model(Cbc.Optimizer)
                    set_optimizer_attribute(model, "logLevel", 0)
                    set_optimizer_attribute(model, "cuts", "off")

                    @variable(model, 0 <= x[i=1:length(iter)], Int)

                    @constraint(model, sum(x.*a) == sum(x.*b))
                    @constraint(model, sum(x.*c) == numMin)
                    @constraint(model, sum(x) == sMax)
                    
                    @objective(model, Max, x[1])
                    optimize!(model)
                    if termination_status(model) == MOI.OPTIMAL
                        x = convert.(Int64, round.(value.(x)))
                        solution = [
                            "One solution is " * join(["x_$i = $(x[i])" for i=iter], ", "),
                            "The system has a non-negative integer solution, so Case 5 is still possible"
                        ]
                    else
                        solution = ["The system has no non-negative integer solutions, so Case 5 is impossible"]
                    end

                    if output > 1
                        printfT("Midpoint Analysis II",
                                "Since |$A| = |$B|, we can set up the following system of equations:",
                                "",
                                equations...,
                                "",
                                solution...)
                    end
                end

                if length(solution) > 1
                    output > 1 && printHeader("CASE 5: GAP ANALYSIS")

                    while true
                        # Find gaps
                        gaps = []
                        for i=1:length(bounds)
                            upper = []
                            lower = []
                            equations = []
                            for int in posInt
                                if int[i] > 0
                                    intConsts = [int...]
                                    intConsts[i] -= 1
                                    (upperConsts, lowerConsts) = (getindex.(bounds, 1), getindex.(bounds, 2))
                                    (potUpper, potLower) = (m//s-sum(upperConsts.*intConsts), m//s-sum(lowerConsts.*intConsts))
                                    append!(upper, potUpper)
                                    append!(lower, potLower)
                                    append!(equations, ["For interval combination $int:",
                                                        "There is a $vMax-sh < $size - $(join(["$(intConsts[j])·$(formatFrac(upperConsts[j], cd))" for j=1:length(int)], " - ")) = $(formatFrac(potUpper, cd))",
                                                        "There is a $vMax-sh > $size - $(join(["$(intConsts[j])·$(formatFrac(lowerConsts[j], cd))" for j=1:length(int)], " - ")) = $(formatFrac(potLower, cd))",
                                                        ""])
                                end
                            end
                            if length(upper) > 0 && length(lower) > 0 && minimum(upper) < maximum(lower)
                                gap = (minimum(upper), maximum(lower))
                                if output > 1
                                    printfT("New Gap",
                                            equations...,
                                            "All are satisifed if there is a gap of $vMax-shs in [$(formatFrac(gap[1], cd)), $(formatFrac(gap[2], cd))]")
                                end
                                append!(gaps, [gap])
                            end
                        end

                        # Break if no change
                        if length(gaps) == 0
                            break
                        end

                        # Insert gaps
                        for gap in gaps
                            (lower, upper) = (gap[1], gap[2])
                            i = 1
                            while i <= length(bounds)
                                fits = false
                                intersectsAt = 0
                                (l, u) = (lower, upper)
                                (bl, bu) = (bounds[i][1], bounds[i][2])
                                if bl < l < u < bu
                                    fits = true
                                elseif bl < l < bu
                                    intersectsAt = 1
                                elseif bl < u < bu
                                    intersectsAt = 2
                                else
                                    (l, u) = (1-upper, 1-lower)
                                    if bl < l < u < bu
                                        fits = true
                                    elseif bl < l < bu
                                        intersectsAt = 1
                                    elseif bl < u < bu
                                        intersectsAt = 2
                                    end
                                end

                                j = findall(x->toFrac(x[2])==bu, intervals)[1]
                                if fits
                                    # Update bounds
                                    insert!(bounds, i+1, [u, bu])
                                    bounds[i][2] = l
                                    # Update intervals
                                    insert!(intervals, j, ["](", formatFrac(u, cd)])
                                    insert!(intervals, j, [")[", formatFrac(l, cd)])
                                elseif intersectsAt == 1
                                    # Update bounds
                                    bounds[i][2] = l
                                    # Update intervals
                                    intervals[j][2] = formatFrac(l, cd)
                                elseif intersectsAt == 2
                                    # Update bounds
                                    bounds[i][1] = u
                                    # Update intervals
                                    intervals[j-1][2] = formatFrac(u, cd)
                                end
                                i += 1
                            end
                        end

                        # Fail if gap finding excessive
                        if length(bounds) > 26
                            output > 0 && printf("Excessive gap finding, VGap failed", line=true)
                            return false
                        end

                        # Update posInt
                        posInt = intCombo(m, s, vMax, bounds, smallBounds, posCombo)
                    end

                    if length(bounds) == 3
                        output > 0 && printf("No further gaps could be generated, VGap failed", line=true)
                        return false
                    end

                    # Update labels and intervalDefs
                    upChr = join('A':'Z')
                    (loChr, loOrd) = (join('z':-1:'a'), 1)
                    labels = repeat(["0"], length(intervals) - 1)
                    intervalDefs = []
                    buddies = []
                    solidInt = 0
                    visited = []
                    for i=1:length(bounds)
                        if !(i in visited)
                            int = bounds[i]
                            chr = upChr[i]
                            k = findall(x->toFrac(x[2])==int[1], intervals)[1]
                            (lower, upper) = (intervals[k][2], intervals[k+1][2])
                            if int == solid
                                labels[k] = "$numMin $vMax-shs"
                                append!(intervalDefs, ["$chr = ($lower, $upper) (|$chr| = $numMin)"])
                                solidInt = i
                            else
                                (chr1, chr2) = (loChr[loOrd], chr)
                                labels[k] = "$chr1 $vMax-shs"
                                append!(intervalDefs, ["$chr2 = ($lower, $upper)"])
                                for j=i:length(bounds)
                                    intBud = bounds[j]
                                    chr3 = upChr[j]
                                    if intBud == [1-int[2], 1-int[1]]
                                        l = findall(x->toFrac(x[2])==intBud[1], intervals)[1]
                                        (lowerBud, upperBud) = (intervals[l][2], intervals[l+1][2])
                                        labels[l] = "$chr1 $vMax-shs"
                                        append!(intervalDefs, ["$chr3 = ($lowerBud, $upperBud) (|$chr2| = |$chr3| = $chr1)"])
                                        append!(buddies, [(i, j)])
                                        append!(visited, j)
                                    end
                                end
                                loOrd += 1
                            end
                        end
                    end

                    if output > 1
                        println()
                        printf("After finding gaps and buddying, this is the interval of the $vMax-shs:")
                        println("\n",
                        interval(intervals...,
                                labels=labels))
                        printLine() 
                        printfT("Note",
                                "We define the following intervals:",
                                sort(intervalDefs)...)
                    end

                    if length(posInt) > 0
                        if output > 1
                            printfT("Gap Analysis I",
                                    "Given the possible small and large $vMax-sh combinations,",
                                    "all combinations of $vMax-shs from the defined intervals are impossible except for:",
                                    "",
                                    posInt...,
                                    "",
                                    "because the range of muffin amounts for the others does not include $size")
                        end
        
                        # Set up and solve system of equations
                        iter = 1:length(posInt)
                        consts = [getindex.(posInt, i) for i=1:length(bounds)]
                        l = solidInt

                        equations = []
                        for (j, k) in buddies
                            append!(equations, [join(["$(consts[j][i])·x_$i" for i=iter], " + ") * " = " * join(["$(consts[k][i])·x_$i" for i=iter], " + ")])
                        end
                        if l > 0
                            append!(equations, [join(["$(consts[l][i])·x_$i" for i=iter], " + ") * " = |$(upChr[l])| = $numMin"])
                        end
                        append!(equations, [join(["x_$i" for i=iter], " + ") * " = s_$vMax = $sMax", ""])

                        append!(equations, ["where x_$i is the # of ($(join(posInt[i], ",")))-students" for i=iter])

                        # Test all possible non-negative integer solutions with system
                        model = Model(Cbc.Optimizer)
                        set_optimizer_attribute(model, "logLevel", 0)
                        set_optimizer_attribute(model, "cuts", "off")

                        @variable(model, 0 <= x[i=1:length(iter)], Int)

                        for (j, k) in buddies
                            @constraint(model, sum(x.*consts[j]) == sum(x.*consts[k]))
                        end
                        if l != 0
                            @constraint(model, sum(x.*consts[l]) == numMin)
                        end
                        @constraint(model, sum(x) == sMax)

                        @objective(model, Max, x[1])
                        optimize!(model)
                        if termination_status(model) == MOI.OPTIMAL
                            x = convert.(Int64, round.(value.(x)))
                            solution = [
                                "One solution is " * join(["x_$i = $(x[i])" for i=iter], ", "),
                                "The system has a non-negative integer solution, so Case 5 is still possible"
                            ]
                        else
                            solution = ["The system has no non-negative integer solutions, so Case 5 is impossible"]
                        end

                        if output > 1
                            printfT("Gap Analysis II",
                                    "Given the new interval equalities, we can set up the following system of equations:",
                                    "",
                                    equations...,
                                    "",
                                    solution...)
                        end

                        if length(solution) > 1
                            output == 1 && printf("Could not generate conclusive system of equations, VGap failed", line=true)
                            return false
                        end
                    else
                        if output > 1
                            printfT("Gap Analysis",
                                    "Given the possible small and large $vMax-sh combinations,",
                                    "all combinations of $vMax-shs from the intervals are impossible since their total amount can not be $size")
                        end
                    end

                end
            else
                if output > 1
                    printfT("Midpoint Analysis",
                            "Given the possible small and large $vMax-sh combinations,",
                            "all combinations of $vMax-shs from intervals A, B, and C are impossible since their total amount can not be $size")
                end
            end

        else
            if output > 1
                printfT("Case 5",
                        "All combinations of small and large $vMax-shs are impossible since their total amount can not be $size")
            end
        end

        # Conclude proof
        alpha = formatFrac(alpha)
        if output > 1
            # Conclude with alpha's value
            printHeader("CONCLUSION")
            printfT("Conclusion",
                    "All possible cases contradict the assumption iff. α ≥ $alpha",
                    "muffins($m,$s) ≤ α, ∀ α ≥ $alpha",
                    "",
                    "muffins($m,$s) ≤ $alpha")
            printEnd()
        elseif output > 0
            printfT("Gap Method",
                    "Upper bound α of muffins($m,$s) is $alpha")
            printEnd()
        end

        true
    end
end

end
