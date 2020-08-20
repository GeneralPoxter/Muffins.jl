module Int

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

export int, vint

# Determines upper bound alpha with Interval Method, optionally outputs proof
# Authors: Antara Hebbar and Jason Liu
function int(m::Int64, s::Int64; output::Int64=2)
    output > 0 && printHeader(center("INTERVAL METHOD"))
    
    if m < s
        alpha = m//s*int(s, m, output=0)
        if output > 1
            printfT("Duality Theorem",
                    "muffins($m,$s) = $m/$s · muffins($s,$m)",
                    "Bounding muffins($s,$m) instead")
            int(s, m, output=output)
        elseif output > 0
            printfT("Interval Method",
                    "Upper bound α of muffins($m,$s) is $(formatFrac(alpha))")
            printEnd()
        end
        return alpha
    elseif m % s == 0
        if output > 0
            printfT("Interval Method",
                    "Since $m % $s = 0, muffins($m,$s) = 1")
            printEnd()
        end
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
        if vint(m, s, alpha, output=output)
            return alpha
        end
    elseif numW < numV
        f = Int64(floor((numV-numW)/sV))                            # Upper bound of minimum # of large V-shs a student can have
        g = Int64(floor(numW/sV))                                   # Lower bound of minimum # of small V-shs a student can have
        alpha = min(((V-f)W + (2f -V-1)m//s)//((V-f)W + (f-1)V),    # Value for alpha derived by solving f(1-x) + (V-f)(1-y) = m/s
                    ((V-g+1)m//s + g - V)//((V-g-1)V + 2g))         # Value for alpha derived by solving gα + (V-g)(1-x) = m/s
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vint(m, s, alpha, output=output)
            return alpha
        end
    end

    if output > 0
        printf("Interval Method inconclusive", line=true)
        printEnd()
    end
    1
end

# Helper function for int -- verifies whether int(m, s, alpha) is conclusive
function vint(m::Int64, s::Int64, alpha::Rational{Int64}; output::Int64=2)
    if m < s || m % s == 0
        output > 0 && printf("VInt does not apply", line=true)
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
            output > 0 && printf("V-Conjecture does not apply, VInt failed", line=true)
            return false
        end

        ((_, x), (y, _)) = findend(m, s, alpha, V)
        xOriginal = m//s - alpha*(V-1)
        yOriginal = m//s - (1-alpha)*(V-2)

        # Check if FindEnd works
        if x != xOriginal && y != yOriginal
            output > 0 && printf("FindEnd inconclusive, VInt failed", line=true)
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
                        "The Interval Method is inconclusive on these intervals, VInt failed")
            end
        end

        # Fail if interval inconclusive
        if x > y || x == alpha || y == 1-alpha
            output == 1 && printf("Could not generate disjoint intervals, VInt failed", line=true)
            return false
        end

        # Define and format variables for proof
        (vMin, vMax, sMin, sMax) = (V, W, sV, sW)
        (f, g) = (Int64(floor(numV/sW)), Int64(floor(diff/sW)))
        (lim1, lim2) = ((vMin)sMin, diff)
        (i, j, k, l) = (xF, yF, y1, x1)
        (rngMin, rngMax, rngS, rngL) = ((alphaF, xF), (x1, alpha1), (yF, y1), (x1, alpha1))
        if numV > numW
            (vMin, vMax, sMin, sMax) = (W, V, sW, sV)
            (f, g) = (Int64(floor(diff/sV)), Int64(floor(numW/sV)))
            (lim1, lim2) = (diff, (vMin)sMin)
            (i, j, k, l) = (y1, x1, xF, yF)
            (rngMin, rngMax, rngS, rngL) = ((yF, alpha1), (alphaF, yF), (alphaF, y1), (x1, xF))
        end
        numMin = (vMin)sMin

        # Conclude interval case
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

        upperB = (vMax-f)*toFrac(rngS[2]) + (f)*toFrac(rngL[2])
        lowerB = (vMax-g)*toFrac(rngL[1]) + (g)*toFrac(rngS[1])
        u = formatFrac(upperB, cd)
        l = formatFrac(lowerB, cd)

        if upperB <= m//s
            if output > 1
                printfT("Case 5.1",
                        "Alice has ≤ $f large $vMax-shs",
                        "She must also have ≥ $(vMax-f) small $vMax-shs, so her maximum amount of muffins is:",
                        "< ($(vMax-f) × $(rngS[2])) + ($f × $(rngL[2])) = $u ≤ $size",
                        "",
                        "Since Alice's muffin amount can not reach $size, this case is impossible")
                printfT("Case 5.2",
                        "All $sMax $vMax-sh students have at least $(f+1) large $vMax-shs",
                        "",
                        "This is impossible because $(f+1)×$sMax = $((f+1)sMax) ≥ $lim1")
            end
        elseif lowerB >= m//s
            if output > 1
                printfT("Case 5.1",
                        "Bob has ≤ $g small $vMax-shs",
                        "He must also have ≥ $(vMax-g) large $vMax-shs, so his minimum amount of muffins is:",
                        "> ($g × $(rngS[1])) + ($(vMax-g) × $(rngL[1])) = $l ≥ $size",
                        "",
                        "Since Bob's muffin amount can not reach $size, this case is impossible")
                printfT("Case 5.2",
                        "All $sMax $vMax-sh students have at least $(g+1) small $vMax-shs",
                        "",
                        "This is impossible because $(g+1)×$sMax = $((g+1)sMax) ≥ $lim2")
            end
        else
            if output > 1
                printfT("Bound # of large $vMax-shs",
                        "All $sMax $vMax-sh students have at least $(f+1) large $vMax-shs",
                        "",
                        "This is impossible because $(f+1)×$sMax = $((f+1)sMax) ≥ $lim1")
                printfT("Negation of prev. bound",
                        "∃ student Alice with ≤ $f large $vMax-shs",
                        "She must also have ≥ $(vMax-f) small $vMax-shs, so her maximum amount of muffins is:",
                        "< ($(vMax-f) × $(rngS[2])) + ($f × $(rngL[2])) = $u",
                        "",
                        "Since $size lies below the interval, this bound is inconclusive")

                printfT("Bound # of small $vMax-shs",
                        "All $sMax $vMax-sh students have at least $(g+1) small $vMax-shs",
                        "",
                        "This is impossible because $(g+1)×$sMax = $((g+1)sMax) ≥ $lim2")
                printfT("Negation of prev. bound",
                        "∃ student Bob with ≤ $g small $vMax-shs",
                        "He must also have ≥ $(vMax-g) large $vMax-shs, so his minimum amount of muffins is:",
                        "> ($g × $(rngS[1])) + ($(vMax-g) × $(rngL[1])) = $l",
                        "",
                        "Since $size lies above the interval, this bound is inconclusive")

                printf("Bounding # of large and small $vMax-shs inconclusive, restarting with individual case analysis", line=true)
            end

            for k=0:vMax
                upperB = (vMax-k)*toFrac(rngL[2]) + (k)*toFrac(rngS[2])
                lowerB = (vMax-k)*toFrac(rngL[1]) + (k)*toFrac(rngS[1]) 
                u = formatFrac(upperB, cd)
                l = formatFrac(lowerB, cd)
                if upperB <= m//s || lowerB >= m//s
                    if output > 1
                        printfT("Case 5.$(k+1)",
                                "Alice has $k small $vMax-shs and $(vMax-k) large $vMax-shs",
                                "Her possible muffin amount lies in:",
                                "",
                                "($k × $(rngS[1]) + $(vMax-k) × $(rngL[1]),",
                                "$k × $(rngS[2]) + $(vMax-k) × $(rngL[2]))",
                                "= ($l, $u)",
                                "",
                                "Since $size lies outside this interval, this case is impossible")
                    end
                else
                    # Fail if interval analysis inconclusive
                    if output > 1
                        printfT("Case 5.$(k+1)",
                                "Bob has $k small $vMax-shs and $(vMax-k) large $vMax-shs",
                                "His possible muffin amount lies in:",
                                "",
                                "($k × $(rngS[1]) + $(vMax-k) × $(rngL[1]),",
                                "$k × $(rngS[2]) + $(vMax-k) × $(rngL[2]))",
                                "= ($l, $u)",
                                "",
                                "Since $size lies inside this interval, this case is inconclusive")
                    elseif output > 0
                        printf("Interval analysis inconclusive, VInt failed", line=true)
                    end
                    return false
                end
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
            printfT("Interval Method",
                    "Upper bound α of muffins($m,$s) is $alpha")
            printEnd()
        end

        true
    end
end

end
