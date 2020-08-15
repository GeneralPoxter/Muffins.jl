module Mid

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

export mid, vmid

# Determines upper bound alpha with Midpoint Method, optionally outputs proof
# Author: Jason Liu
function mid(m::Int64, s::Int64; output::Int64=2)
    output > 0 && printHeader(center("MIDPOINT METHOD"))

    if m < s
        if output > 0
            printf("Midpoint Method does not apply", line=true)
            printEnd()
        end
        return Nothing
    elseif m % s == 0
        if output > 0
            printfT("Midpoint Method",
                    "Since $m % $s = 0, muffins($m,$s) = 1")
            printEnd()
        end
        return 1
    end

    (V, W, sV, sW) = sv(m, s)
    numV = (V)sV
    numW = (W)sW

    # Compute potential alpha candidates
    alphas = []
    if numW > numV
        for (a, b, c) in comboTup(W, 3)
            append!(alphas, (a//2 + (W)b + c - (1+b)m//s)//((W-1)b + c))            # Value for alpha derived by solving a(1/2) + b(1-y) + c(1-alpha) = m/s
            append!(alphas, ((1-a+c)m//s + (W-1)a - b//2 -c)//((W-1)a + (V-1)c))    # Value for alpha derived by solving a(y) + b(1/2) + c(1-x) = m/s
        end
    elseif numW < numV
        for (a, b, c) in comboTup(V, 3)
            append!(alphas, ((W)a + b//2 - (1+a-c)m//s)//((W-1)a + (V-1)c))         # Value for alpha derived by solving a(1-y) + b(1/2) + c(x) = m/s
            append!(alphas, ((1+b)m//s - b - c//2)//(a + (V-1)b))                   # Value for alpha derived by solving a(alpha) + b(1-x) + c(1/2) = m/s
        end
    end

    # Test alpha candidates
    for alpha in sort(unique(alphas))
        if denominator(alpha) != 0 && vmid(m, s, alpha, output=0)
            vmid(m, s, alpha, output=output)
            return alpha
        end
    end

    if output > 0
        printf("All α candidates were inconclusive, Midpoint Method inconclusive", line=true)
        printEnd()
    end
    1
end

# Helper function for mid -- verifies whether mid(m, s, alpha) is conclusive
function vmid(m::Int64, s::Int64, alpha::Rational{Int64}; output::Int64=2)
    if m < s || m % s == 0
        output > 0 && printf("VMid does not apply", line=true)
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
        
        # Initialize Interval Method proof
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
            output > 0 && printf("V-Conjecture does not apply, VMid failed", line=true)
            return false
        end
        
        ((_, x), (y, _)) = findend(m, s, alpha, V)
        xOriginal = m//s - alpha*(V-1)
        yOriginal = m//s - (1-alpha)*(V-2)

        # Check if FindEnd works
        if x != xOriginal && y != yOriginal
            output > 0 && printf("FindEnd inconclusive, VMid failed", line=true)
            return false
        end

        # Define and format variables for proof
        cd = lcm(s, denominator(x), denominator(y))
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
                        "The Midpoint Method is inconclusive on these intervals, VMid failed")
            end
        end
        
        # Fail if interval inconclusive
        if x > y || x == alpha || y == 1-alpha
            output == 1 && printf("Could not generate disjoint intervals, VMid failed", line=true)
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

            posInt = []
            if numW > numV
                if output > 1
                    println()
                    printf("The following intervals capture what we know about the $W-shs:")
                    println("\n",
                    interval(["(", j],
                            ["|", mid],
                            [")[", k],
                            ["](", l],
                            [")", alpha1],
                            labels=["z $W-shs", "z $W-shs", "0", "$numV $W-shs"]))
                    printLine()
                    printfT("Note",
                            "We define the following intervals:",
                            "A = ($j,$mid)",
                            "B = ($mid,$k) (|A| = |B| = z)",
                            "C = ($l,$alpha1) (|C| = $numV)")
                end

                # Determine possible interval combinations
                for (a, b, c) in comboTup(W, 3)
                    upperB = a*1//2 + b*toFrac(k) + c*(1-alpha)
                    lowerB = a*toFrac(j) + b*1//2 + c*toFrac(l)
                    if a+b in posCombo && upperB > m//s > lowerB
                        append!(posInt, [(a, b, c)])
                    end
                end
            elseif numW < numV
                if output > 1
                    println()
                    printf("The following intervals capture what we know about the $V-shs:")
                    println("\n",
                    interval(["(", alphaF],
                            [")[", i],
                            ["](", j],
                            ["|", mid],
                            [")", k],
                            labels=["$numW $V-shs", "0", "z $V-shs", "z $V-shs"]))
                    printLine()
                    printfT("Note",
                            "We define the following intervals:",
                            "A = ($alphaF,$i) (|A| = $numW)",
                            "B = ($j,$mid)",
                            "C = ($mid,$k) (|B| = |C| = z)")
                end

                # Determine possible interval combinations
                for (a, b, c) in comboTup(V, 3)
                    upperB = a*toFrac(i) + b*1//2 + c*toFrac(k)
                    lowerB = a*alpha + b*toFrac(j) + c*1//2
                    if a in posCombo && upperB > m//s > lowerB
                        append!(posInt, [(a, b, c)])
                    end
                end
            end

            if length(posInt) > 0
                if output > 1
                    combos = ["$a $vMax-shs from A, $b from B, and $c from C" for (a, b, c) in posInt]
                    printfT("Midpoint Analysis I",
                            "Given the possible small and large $vMax-sh combinations,",
                            "all combinations of $vMax-shs from intervals A, B, and C are impossible except for:",
                            "",
                            combos...,
                            "",
                            "because the range of muffin amounts for the others does not include $size")
                end

                # Check if posInt is too large
                if length(posInt) > 5
                    output > 0 && printf("The # of possible interval combinations is too large, VMid failed", line=true)
                    return false
                end

                # Set up and solve system of equations
                (a, b, c) = (getindex.(posInt, 1), getindex.(posInt, 2), getindex.(posInt, 3))
                (A, B, C) = ("A", "B", "C")
                if numW < numV
                    (a, b, c) = (b, c, a)
                    (A, B, C) = (B, C, A)
                end

                iter = 1:length(posInt)
                definitions = []
                for i=iter
                    append!(definitions, ["where x_$i is the # of students with", "$(a[i]) $A-shs, $(b[i]) $B-shs, $(c[i]) $C-shs"])
                end
                equations = [
                    join(["$(a[i])·x_$i" for i=iter], " + ") * " = " * join(["$(b[i])·x_$i" for i=iter], " + "),
                    join(["$(c[i])·x_$i" for i=iter], " + ") * " = |$C| = $numMin",
                    join(["x_$i" for i=iter], " + ") * " = s_$vMax = $sMax",
                    "",
                    definitions...
                ]

                solution = []
                for x in combo(sMax, length(iter))
                    if sum(x.*a) == sum(x.*b) && sum(x.*c) == numMin
                        solution = [
                            "One solution is " * join(["x_$i = $(x[i])" for i=iter], ", "),
                            "The system has a non-negative integer solution, so Case 5 is still possible, VMid failed"
                        ]
                        break
                    end
                end
                if length(solution) == 0
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

                if length(solution) > 1
                    output == 1 && printf("Could not generate conclusive system of equations, VMid failed", line=true)
                    return false
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
            printfT("Midpoint Method",
                    "Upper bound α of muffins($m,$s) is $alpha")
            printEnd()
        end

        true
    end
end

# Helper function for mid and vmid -- determines all non-negative integer combinations of size k that sum to T
function combo(T, k)
    if k == 0
        return [[]]
    elseif k == 1
        return [[T]]
    elseif T == 0
        return [repeat([0], k)]
    else
        return hcat([vcat.([i], combo(T-i, k-1)) for i=0:T]...)
    end
end

# Helper function for mid and vmid -- convert the results of combo(T, k) into tuples
function comboTup(T, k)
    return [tuple(x...) for x in combo(T, k)]
end

end
