module Mid

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

export mid, vmid

# Determines upper bound alpha with Midpoint Method, optionally outputs proof
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
        for c=0:W, b=0:(W-c)
            a = W-b-c
            append!(alphas, (a//2 + (W)b + c - (1+b)m//s)//((W-1)b + c))            # Value for alpha derived by solving a(1/2) + b(1-y) + c(1-alpha) = m/s
            append!(alphas, ((1-a+c)m//s + (W-1)a - b//2 -c)//((W-1)a + (V-1)c))    # Value for alpha derived by solving a(y) + b(1/2) + c(1-x) = m/s
        end
    elseif numW < numV
        for c=0:V, b=0:(V-c)
            a = V-b-c
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
        printf("Midpoint Method inconclusive", line=true)
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
        output > 0 && printfT("Theorem 4.5", "For m ≥ s, α must be ≥ 1/3")
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

            # Establish assumptions and premises
            printHeader("OVERVIEW")
            printfT("Goal", 
                    "Prove:",
                    "muffins($m,$s) ≤ α = $alphaF",
                    "by contradicting the assumption")
            printfT("Assumption", 
                    "Assume:",
                    "The desired upper bound is α",
                    "muffins($m,$s) > α ≥ 1/3")
            printfT("Theorem 2.6.2", 
                    "Since muffins($m,$s) > 1/3, each muffin must be cut into 2 shs, totaling $(2m) shs")
            printfT("Property of Buddies",
                    "Since each muffin is cut into 2 shs that are buddies, each sh of size x must imply the existence of a sh of size 1-x")
        end
        
        # Check if V-Conjecture applies
        if m//s * 1//(V+1) > alpha || 1 - m//s * 1//(W-1) > alpha
            output > 0 && printf("V-Conjecture does not apply, VMid failed", line=true)
            return false
        end
        
        ((_, x), (y, _)) = findend(m, s, alpha, V)

        # Check if FindEnd works
        if x == alpha && y == 1-alpha
            output > 0 && printf("FindEnd inconclusive, VMid failed", line=true)
            return false
        end

        # Define and format variables for proof
        cd = lcm(s, denominator(x), denominator(y))
        alphaF = formatFrac(alpha, cd)
        alpha1 = formatFrac(1-alpha, cd)
        size = formatFrac(m//s, cd)
        a = formatFrac(m//s-x, cd)
        b = formatFrac(m//s-y, cd)
        xF = formatFrac(x, cd)
        x1 = formatFrac(1-x, cd)
        yF = formatFrac(y, cd)
        y1 = formatFrac(1-y, cd)
        diff = abs(numV-numW)

        # Continue proof
        if output > 1
            # Describe casework
            printHeader("CASEWORK")

            printfT("V-Conjecture",
                    "The only cases that need to be considered deal with everyone having either $W or $V shs, so:",
                    "",
                    "$(W)·s_$W + $(V)·s_$V = $(2m)  (total shs)",
                    "s_$W + s_$V = $s  (total students)",
                    "where s_N = # of students with N shs",
                    "",
                    "The solution to the system is:",
                    "s_$W = $sW, s_$V = $sV",
                    "So there are $numW $W-shs and $numV $V-shs")

            if x != alpha
                printfT("Case 1",
                        "Alice has a $V-sh ≥ $xF",
                        "Her other $(V-1) $V-shs sum to ≤ ($size - $xF) = $a",
                        "One of them is ≤ ($a × 1/$(V-1)) = $alphaF",
                        "",
                        "Contradicts assumption if α ≥ $alphaF")
            else
                printfT("Case 1",
                        "FindEnd did not produce a conclusive bound for $V-shs")
            end

            if y != 1-alpha
                printfT("Case 2",
                        "Bob has a $W-sh ≤ $yF",
                        "His other $(W-1) $W-shs sum to ≥ ($size - $yF) = $b",
                        "One of them is ≥ ($b × 1/$(W-1)) = $alpha1",
                        "Its buddy is ≤ (1 - $alpha1) = $alphaF",
                        "",
                        "Contradicts assumption if α ≥ $alphaF")
            else
                printfT("Case 2",
                        "FindEnd did not produce a conclusive bound for $W-shs")
            end

            printHeader("CASE 3: INTERVAL ANALYSIS")
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
                end
                if yF != alpha1
                    println("\n",
                            interval(["(", alphaF],
                                    ["](", yF],
                                    [")", alpha1],
                                    labels=["0 $W-shs", "$numW $W-shs"]))
                end

                printfT("Case 3",
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
                    "Because $numMin $vMin-shs lie in ($(rngMin[1]),$(rngMin[2])), $numMin $vMax-shs must lie in ($(rngMax[1]),$(rngMax[2]))",
                    "",
                    "Similary, the gap that lies in [$xF,$yF] implies a gap that lies in [$y1,$x1]")
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
                printfT("Case 3",
                        "All combinations of small and large $vMax-shs are impossible except for:",
                        "",
                        combos...,
                        "",
                        "because the range of muffin amounts for the others does not include $size")

                printHeader("CASE 3: MIDPOINT ANALYSIS")
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
                for c=0:W, b=0:(W-c)
                    a = W-b-c
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
                for c=0:V, b=0:(V-c)
                    a = V-b-c
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

                # Determine if a solvable system of equations is possible
                # i.e. there are at most 3 possible student types to match 3 intervals
                if length(posInt) > 3
                    if output > 1
                        printfT("System of equations",
                                "A solvable system of equations could not be set up to see if the above combinations will result in a contradictory non-integer solution,",
                                "VMid failed")
                    elseif output > 0
                        printf("Could not generate conclusive system of equations, VMid failed", line=true)
                    end
                    return false
                end

                # Set up and solve system of equations
                equations = []
                solutions = []
                fail = false
                (a, b, c) = (getindex.(posInt, 1), getindex.(posInt, 2), getindex.(posInt, 3))
                (z1, Z1, z2, Z2, z3, Z3) = (a, "A", b, "B", c, "C")
                if numW < numV
                    (z1, Z1, z2, Z2, z3, Z3) = (b, "B", c, "C", a, "A")
                end

                if length(posInt) == 3
                    x1 = formatFrac(((z1[3]-z1[2]+z2[2]-z2[3])numMin + ((z2[3]-z1[3])z3[2]+(z1[2]-z2[2])z3[3])sMax)//((z1[3]-z1[2]+z2[2]-z2[3])z3[1] + (z1[1]-z1[3]+z2[3]-z2[1])z3[2] + (z1[2]-z1[1]+z2[1]-z2[2])z3[3]))
                    x2 = formatFrac(((z1[3]-z2[3])numMin - ((z1[3]-z2[3])z3[1] + (z2[1]-z1[1])z3[3])*toFrac(x1))//((z1[3]-z2[3])z3[2] + (z2[2]-z1[2])z3[3]))
                    x3 = formatFrac(sMax-toFrac(x1)-toFrac(x2))

                    equations = ["$(z1[1])·x + $(z1[2])·y + $(z1[3])·z = $(z2[1])·x + $(z2[2])·y + $(z2[3])·z",
                                "$(z3[1])·x + $(z3[2])·y + $(z3[3])·z = |$Z3| = $numMin",
                                "x + y + z = s_$vMax = $sMax",
                                "",
                                "where x is the # of students with",
                                "$(a[1]) A-shs, $(b[1]) B-shs, and $(c[1]) C-shs",
                                "and y the # of students with",
                                "$(a[2]) A-shs, $(b[2]) B-shs, and $(c[2]) C-shs",
                                "and z the # of students with",
                                "$(a[3]) A-shs, $(b[3]) B-shs, and $(c[3]) C-shs"]

                    if occursin("/", x1) || occursin("/", x2) || toFrac(x1) < 0 || toFrac(x2) < 0 || toFrac(x3) < 0
                        solutions = ["The solutions are x = $x1, y = $x2, z = $x3",
                                    "The solutions are not positive integers, so the entirety of Case 3 is impossible"]
                    else
                        solutions = ["The solutions are x = $x1, y = $x2, z = $x3",
                                    "The solutions are positive integers, so Case 3 is still possible, VMid failed"]
                        fail = true
                    end
                end
                
                if length(posInt) == 2
                    x1 = formatFrac(sMax//(1+(z1[1]-z2[1])//(z2[2]-z1[2])))
                    x2 = formatFrac(sMax-toFrac(x1))

                    equations = ["$(z1[1])·x + $(z1[2])·y = $(z2[1])·x + $(z2[2])·y",
                                "x + y = s_$vMax = $sMax",
                                "",
                                "where x is the # of students with",
                                "$(a[1]) A-shs, $(b[1]) B-shs, and $(c[1]) C-shs",
                                "and y the # of students with",
                                "$(a[2]) A-shs, $(b[2]) B-shs, and $(c[2]) C-shs"]
                    
                    if occursin("/", x1) || toFrac(x1) < 0 || toFrac(x2) < 0 
                        solutions = ["The solutions are x = $x1, y = $x2",
                                    "The solutions are not positive integers, so the entirety of Case 3 is impossible"]
                    elseif z3[1]*toFrac(x1) + z3[2]*toFrac(x2) != numMin
                        insert!(equations, 3, "$(z3[1])·x + $(z3[2])·y = |$Z3| = $numMin")
                        solutions = ["This system has no solutions, so the entirety of Case 3 is impossible"]
                    else
                        solutions = ["The solutions are x = $x1, y = $x2", 
                                    "The solutions are positive integers, so Case 3 is still possible, VMid failed"]
                        fail = true
                    end
                end

                if length(posInt) == 1
                    equations = ["$(z1[1])·x = $(z2[1])·x",
                                "x = s_$vMax = $sMax",
                                "",
                                "where x is the # of students with $(a[1]) A-shs, $(b[1]) B-shs, and $(c[1]) C-shs"]
                    
                    if z1[1] != z2[1]
                        solutions = ["This system has no solution, so the entirety of Case 3 is impossible"]
                    else
                        solutions = ["This system has infinite solutions, VMid failed"]
                        fail = true
                    end
                end

                if output > 1
                    printfT("Midpoint Analysis II",
                            "Since |$Z1| = |$Z2|, we can set up the following system of equations:",
                            "",
                            equations...,
                            "",
                            solutions...)
                end

                if fail
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
                printfT("Case 3",
                        "All combinations of small and large $vMax-shs are impossible since their total amount can not be $size")
            end
        end

        # Conclude proof
        alpha = formatFrac(alpha)
        if output > 1
            # Conclude with alpha's value
            printHeader("CONCLUSION")
            printfT("Compute α",
                    "Each possible case derives the same lower bound for α that contradicts the assumption",
                    "",
                    "All possible cases contradict the assumption iff.",
                    "α ≥ $alpha")
            printfT("Conclusion",
                    "muffins($m,$s) ≤ α, ∀ α ≥ $alpha",
                    "",
                    "muffins($m,$s) ≤ $alpha")
            printEnd()
        elseif output > 0
            printfT("Midpoint Method",
                    "Upper bound of muffins($m,$s) is $alpha")
            printEnd()
        end

        true
    end
end

end
