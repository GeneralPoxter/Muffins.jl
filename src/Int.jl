module Int

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

export int, vint

# Determines upper bound with Interval Method, optinally outputs proof
function int(m::Int64, s::Int64, proof::Bool=true)
    printHeader(center("INTERVAL METHOD"))
    
    if m < s
        printf("Interval Method does not apply", line=true)
        printEnd()
        return Nothing
    elseif m % s == 0
        printfT("Interval Method",
                "Since $m % $s = 0, muffins($m,$s) = 1")
        printEnd()
        return 1
    end

    (V, W, sV, sW) = sv(m, s)
    numV = (V)sV
    numW = (W)sW

    # Derive alpha using Int Algorithm
    if numW > numV
        f = Int64(floor(numV/sW))                                   # Upper bound of minimum # of large W-shs a student can have
        g = Int64(floor((numW-numV)/sW))                            # Lower bound of minimum # of small W-shs a student can have
        alpha = min(((W-f)W - (W-f+1)m//s + f)//((W-f-1)W + 2f),    # Value for alpha derived by solving f(1-α) + (W-f)(1-y) = m/s
                    ((g-1)W + (W -2g+1)m//s)//(W^2 - g))            # Value for alpha derived by solving gy + (W-g)(1-x) = m/s
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vint(m, s, alpha, proof)
            return alpha
        end
    elseif numW < numV
        f = Int64(floor((numV-numW)/sV))                            # Upper bound of minimum # of large V-shs a student can have
        g = Int64(floor(numW/sV))                                   # Lower bound of minimum # of small V-shs a student can have
        alpha = min(((V-f)W + (2f -V-1)m//s)//((V-f)W + (f-1)V),    # Value for alpha derived by solving f(1-x) + (V-f)(1-y) = m/s
                    ((V-g+1)m//s + g - V)//((V-g-1)V + 2g))         # Value for alpha derived by solving gα + (V-g)(1-x) = m/s
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vint(m, s, alpha, proof)
            return alpha
        end
    end

    printf("V-Conjecture inconclusive, Interval Method inconclusive", line=true)
    printEnd()
    1
end

# Helper function for int -- verifies whether int(m, s, alpha) is conclusive
function vint(m::Int64, s::Int64, alpha::Rational{Int64}, proof::Bool=true)
    if m < s || m % s == 0
        printf("VInt does not apply", line=true)
        false
    elseif alpha < 1/3
        printfT("Theorem 4.5", 
                "For m ≥ s, α must be ≥ 1/3")
        false
    elseif alpha > 1
        printfT("",
                "α must be ≤ 1")
        false
    else
        (V, W, sV, sW) = sv(m, s)
        numV = (V)sV
        numW = (W)sW
        
        # Initialize Interval Method proof
        if proof
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
            printf("V-Conjecture does not apply, VInt failed", line=true)
            return false
        end

        ((_, x), (y, _)) = findend(m, s, alpha, V)

        # Check if V-Conjecture works
        if (m//s-x) * 1//(V-1) != alpha || 1 - (m//s-y) * 1//(W-1) != alpha
            printf("V-Conjecture inconclusive, VInt failed", line=true)
            return false
        end

        # Continue proof
        cd = lcm(s, denominator(x), denominator(y))
        genInt = true
        if proof
            # Define and format variables for proof
            alphaF = formatFrac(alpha, cd)
            alpha1 = formatFrac(1-alpha, cd)
            size = formatFrac(m//s, cd)
            a = formatFrac(m//s-x, cd)
            b = formatFrac(m//s-y, cd)
            xF = formatFrac(x, cd)
            yF = formatFrac(y, cd)

            # Describe casework
            printHeader("CASEWORK")

            printfT("V-Conjecture",
                    "The only cases that need to be considered deal with everyone having either $W or $V shs, so:",
                    "",
                    "$(W)s_$W + $(V)s_$V = $(2m)  (total shs)",
                    "s_$W + s_$V = $s  (total students)",
                    "where s_N = # of students with N shs",
                    "",
                    "The solution to the system is:",
                    "s_$W = $sW, s_$V = $sV",
                    "So there are $numW $W-shs and $numV $V-shs")

            printfT("Case 1",
                    "Alice has a $V-sh ≥ $xF",
                    "Her other $(V-1) $V-shs sum to ≤ ($size - $xF) = $a",
                    "One of them is ≤ ($a × 1/$(V-1)) = $alphaF",
                    "",
                    "Contradicts assumption if α ≥ $alphaF")
            printfT("Case 2",
                    "Bob has a $W-sh ≤ $yF",
                    "His other $(W-1) $W-shs sum to ≥ ($size - $yF) = $b",
                    "One of them is ≥ ($b × 1/$(W-1)) = $alpha1",
                    "Its buddy is ≤ (1 - $alpha1) = $alphaF",
                    "",
                    "Contradicts assumption if α ≥ $alphaF")

            printHeader("CASE 3: INTERVAL ANALYSIS")
            println()
            printf("The following intervals capture the negation of the previous cases:")
            if x <= y && xF > alphaF && yF < alpha1
                println("\n",
                        interval(["(", alphaF],
                                [")[", xF],
                                ["](", yF],
                                [")", alpha1],
                                labels=["$numV $V-shs", "0", "$numW $W-shs"]))
                printLine()
            elseif xF == alphaF && yF == alpha1
                println("\n",
                            center("There is no conclusive negation"))
                printfT("Case 3",
                        "This case does not exist")
                genInt = false
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
                
                # Fail if intervals inconclusive
                if proof
                    printfT("Case 3",
                            "The Interval Method is inconclusive on these intervals, VInt failed")
                else
                    printf("Could not generate conclusive interval, VInt failed", line=true)
                end

                return false
            end
        end

        # Conclude Case 3 (interval case)
        if proof && genInt
            # Define and format variables for proof
            x1 = formatFrac(1-x, cd)
            y1 = formatFrac(1-y, cd)
            diff = abs(numV-numW)

            (vMin, vMax, sMin, sMax) = (V, W, sV, sW)
            (f, g) = (Int64(floor(numV/sW)), Int64(floor(diff/sW)))
            (lim1, lim2) = ((vMin)sMin, diff)
            (i, j, k, l) = (xF, yF, y1, x1)
            (rngMin, rngMax, rngS, rngL) = ((alphaF, xF), (x1, alpha1), (yF, y1), (x1, alpha1))
            if numV > numW
                (vMin, vMax, sMin, sMax) = (W, V, sW, sV)
                (f, g) = (Int64(floor(diff/sV)), Int64(floor(numW/sV)))
                (lim1, lim2) = (lim2, lim1)
                (i, j, k, l) = (y1, x1, xF, yF)
                (rngMin, rngMax, rngS, rngL) = ((yF, alpha1), (alphaF, yF), (alphaF, y1), (x1, xF))
            end
            numMin = (vMin)sMin

            # Conclude Case 3 (interval case)
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

            upperB = (vMax-f)*toFrac(rngS[2]) + (f)*toFrac(rngL[2])
            lowerB = (vMax-g)*toFrac(rngL[1]) + (g)*toFrac(rngS[1])
            u = formatFrac(upperB, cd)
            l = formatFrac(lowerB, cd)

            if upperB <= m//s
                printfT("Case 3.1",
                        "All $sMax $vMax-sh students have at least $(f+1) large $vMax-shs",
                        "",
                        "This is impossible because $(f+1)×$sMax = $((f+1)sMax) ≥ $lim1")
                printfT("Case 3.2",
                        "∃ student Alice with ≤ $f large $vMax-shs",
                        "She must also have ≥ $(vMax-f) small $vMax-shs, so her maximum amount of muffins is:",
                        "< ($(vMax-f) × $(rngS[2])) + ($f × $(rngL[2])) = $u",
                        "",
                        "Since Alice's muffin amount can not reach $size, this case is impossible")
            elseif lowerB >= m//s
                printfT("Case 3.1",
                        "All $sMax $vMax-sh students have at least $(g+1) small $vMax-shs",
                        "",
                        "This is impossible because $(g+1)×$sMax = $((g+1)sMax) ≥ $lim2")
                printfT("Case 3.2",
                        "∃ student Bob with ≤ $g small $vMax-shs",
                        "He must also have ≥ $(vMax-g) large $vMax-shs, so his minimum amount of muffins is:",
                        "> ($g × $(rngS[1])) + ($(vMax-g) × $(rngL[1])) = $l",
                        "",
                        "Since Bob's muffin amount can not reach $size, this case is impossible")
            else 
                printfT("Case 3.1",
                        "All $sMax $vMax-sh students have at least $(f+1) large $vMax-shs",
                        "",
                        "This is impossible because $(f+1)×$sMax = $((f+1)sMax) ≥ $lim1")
                printfT("Negation of Case 3.1",
                        "∃ student Alice with ≤ $f large $vMax-shs",
                        "She must also have ≥ $(vMax-f) small $vMax-shs, so her maximum amount of muffins is:",
                        "< ($(vMax-f) × $(rngS[2])) + ($f × $(rngL[2])) = $u",
                        "",
                        "Since $size lies below the upper bound, this case is inconclusive")
                printfT("Case 3.2",
                        "All $sMax $vMax-sh students have at least $(g+1) small $vMax-shs",
                        "",
                        "This is impossible because $(g+1)×$sMax = $((g+1)sMax) ≥ $lim2")
                printfT("Negation of Case 3.2",
                        "∃ student Bob with ≤ $g small $vMax-shs",
                        "He must also have ≥ $(vMax-g) large $vMax-shs, so his minimum amount of muffins is:",
                        "> ($g × $(rngS[1])) + ($(vMax-g) × $(rngL[1])) = $l",
                        "",
                        "Since $size lies above the lower bound, this case is inconclusive")

                printf("Bounding # of large and small $vMax-shs inconclusive, proceeding with individual case analysis", line=true)
                for k=0:vMax
                    upperB = (vMax-k)*toFrac(rngL[2]) + (k)*toFrac(rngS[2])
                    lowerB = (vMax-k)*toFrac(rngL[1]) + (k)*toFrac(rngS[1]) 
                    u = formatFrac(upperB, cd)
                    l = formatFrac(lowerB, cd)
                    if upperB <= m//s || lowerB >= m//s
                        printfT("Case 3.$(k+3)",
                                "Alice has $k small $vMax-shs and $(vMax-k) large $vMax-shs",
                                "Her possible muffin amount lies in:",
                                "",
                                "($k × $(rngS[1]) + $(vMax-k) × $(rngL[1]),",
                                "$k × $(rngS[2]) + $(vMax-k) × $(rngL[2]))",
                                "= ($l, $u)",
                                "",
                                "Since $size lies outside this interval, this case is impossible")
                    else
                        printfT("Case 3.$(k+3)",
                                "Bob has $k small $vMax-shs and $(vMax-k) large $vMax-shs",
                                "His possible muffin amount lies in:",
                                "",
                                "($k × $(rngS[1]) + $(vMax-k) × $(rngL[1]),",
                                "$k × $(rngS[2]) + $(vMax-k) × $(rngL[2]))",
                                "= ($l, $u)",
                                "",
                                "Since $size lies inside this interval, this case is inconclusive")
                        printf("Interval analysis inconclusive, VInt failed", line=true)
                        return false
                    end
                end
            end
        end

        # Conclude proof
        alpha = formatFrac(alpha)
        if proof
            # Conclude with alpha's value
            printHeader("CONCLUSION")
            printfT("Compute α",
                    "Each possible case derive the same lower bound for α that contradicts the assumption",
                    "",
                    "All possible cases contradict the assumption iff.",
                    "α ≥ $alpha")
            printfT("Conclusion",
                    "muffins($m,$s) ≤ α, ∀ α ≥ $alpha",
                    "",
                    "muffins($m,$s) ≤ $alpha")
        else
            printfT("Interval Method",
                    "Upper bound of muffins($m,$s) is $alpha")
        end
        printEnd()

        true
    end
end

end
