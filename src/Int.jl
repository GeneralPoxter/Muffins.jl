module Int

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

export int, intproof, vint

# Determines upper bound with Interval Method, optinally outputs proof
function int(m, s, proof=true)
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
    alpha = 1
    if numW > numV
        f = Int64(floor(numV/sW))
        alpha = min(((W-f)W - (W-f+1)m//s + f)//((W-f-1)W + 2f),
                    ((V)m//s - V - (W-f-3)W -2f -1)//((V -2W +2f +2)W - f - 1))
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vint(m, s, alpha)
            return output(m, s, alpha, proof)
        end
    elseif numW < numV
        f = Int64(floor((numV-numW)/sV))
        alpha = ((V-f)W + (2f -V-1)m//s)//((V-f)W + (f-1)V)
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vint(m, s, alpha)
            return output(m, s, alpha, proof)
        end
    end

    printf("Interval Method was inconclusive", line=true)
    printEnd()
    alpha
end

# Helper function for int -- outputs Int Method conclusion
function output(m, s, alpha, proof)
    if proof
        intproof(m, s, alpha)
    else
        printfT("Interval Method",
                "Upper bound of muffins($m,$s) is $(formatFrac(alpha))")
        printEnd()
    end
    alpha
end

# Helper function for int -- determines whether int(m, s, alpha) is conclusive
function vint(m, s, alpha)
    if alpha < 1/3
        false
    else
        (V, W, sV, sW) = sv(m, s)

        if m//s * 1//(V+1) > alpha || 1 - m//s * 1//(V-2) > alpha
            return false
        end

        ((_, x), (y, _)) = findend(m, s, alpha, V)

        if alpha > x || x > y || y > 1-alpha
            false
        else
            true
        end
    end
end

# Helper function for int -- generates proof of Interval Method
function intproof(m, s, alpha)
    if !vint(m, s, alpha)
        printf("Cannot generate proof with given input")
        return
    end

    # Define and format variables for proof
    (V, W, sV, sW) = sv(m, s)
    numV = (V)sV
    numW = (W)sW
    diff = abs(numV-numW)
    ((_, x), (y, alpha1)) = findend(m, s, alpha, V)
    size = formatFrac(m//s)
    alpha = formatFrac(alpha)
    alpha1 = formatFrac(alpha1)
    a = formatFrac(m//s-x)
    b = formatFrac(m//s-y)
    x1 = formatFrac(1-x)
    x = formatFrac(x)
    y1 = formatFrac(1-y)
    y = formatFrac(y)

    (vMin, vMax, sMin, sMax) = (V, W, sV, sW)
    f = Int64(floor(numV/sW))
    lim = (vMin)sMin
    (i, j, k, l) = (x, y, y1, x1)
    (rngMin, rngMax, rngS, rngL) = ((alpha, x), (x1, alpha1), (y, y1), (x1, alpha1))
    if numV > numW
        (vMin, vMax, sMin, sMax) = (W, V, sW, sV)
        f = Int64(floor(diff/sV))
        lim = diff
        (i, j, k, l) = (y1, x1, x, y)
        (rngMin, rngMax, rngS, rngL) = ((y, alpha1), (alpha, y), (alpha, y1), (x1, x))
    end
    numMin = (vMin)sMin

     # Establish assumptions and premises
    printHeader("OVERVIEW")
    printfT("Goal", 
            "Prove:",
            "muffins($m,$s) ≤ α = $alpha",
            "by contradicting the assumption")
    printfT("Assumption", 
            "Assume:",
            "The desired upper bound is α",
            "muffins($m,$s) > α ≥ 1/3")
    printfT("Theorem 2.6.2", 
            "Since muffins($m,$s) > 1/3, each muffin must be cut into 2 shs, totaling $(2m) shs")
    printfT("Property of Buddies",
            "Since each muffin is cut into 2 shs that are buddies, each sh of size x must imply the existence of a sh of size 1-x")

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
            "Alice has a $V-sh ≥ $x",
            "Her other $(V-1) $V-shs sum to ≤ ($size - $x) = $a",
            "One of them is ≤ ($a × 1/$(V-1)) = $alpha",
            "",
            "Contradicts assumption if α ≥ $alpha")
    printfT("Case 2",
            "Bob has a $W-sh ≤ $y",
            "His other $(W-1) $W-shs sum to ≥ ($size - $y) = $b",
            "One of them is ≥ ($b × 1/$(W-1)) = $alpha1",
            "Its buddy is ≤ (1 - $alpha1) = $alpha",
            "",
            "Contradicts assumption if α ≥ $alpha")

    printHeader("CASE 3: INTERVAL ANALYSIS")
    printf("The following intervals capture the negation of the previous cases:")
    println("\n",
            interval(["(", alpha],
                    [")[", x],
                    ["](", y],
                    [")", alpha1],
                    labels=["$numV $V-shs", "0", "$numW $W-shs"]))
    printLine()

    printfT("Property of Buddies",
            "Because $numMin $vMin-shs lie in ($(rngMin[1]), $(rngMin[2])), $numMin $vMax-shs must lie in ($(rngMax[1]), $(rngMax[2]))",
            "Similary, the gap that lies in [$x, $y] implies a gap that lies in [$y1, $x1]")
    printf("The following intervals capture the previous statements:")
    println("\n",
            interval(["(", alpha],
                    [")[", i],
                    ["](", j],
                    [")[", k],
                    ["](", l],
                    [")", alpha1],
                    labels=["$numMin $V-shs", "0", "$diff $vMax-shs", "0", "$numMin $W-shs"]))
    printLine()

    printfT("Note",
            "Let the $vMax-shs that lie in ($(rngS[1]), $(rngS[2])) be small-shs",
            "Let the $vMax-shs that lie in ($(rngL[1]), $(rngL[2])) be large-shs")

    printfT("Case 3.1",
            "All $sMax $vMax-sh students have at least $(f+1) large-shs",
            "",
            "This is impossible because $(f+1)×$sMax = $((f+1)sMax) ≥ $lim")
        
    upperB = (vMax-f)*toFrac(rngS[2]) + (f)*toFrac(rngL[2])
    if upperB <= toFrac(size)
        printfT("Case 3.2",
                "Alice has ≤ $f large-shs",
                "She must also have ≥ $(vMax-f) small-shs, so her maximum amount of muffins is:",
                "< ($(vMax-f) × $(rngS[2])) + ($f × $(rngL[2])) = $(formatFrac(upperB))",
                "",
                "Since Alice's muffin amount can not reach $size, this case is impossible")
    else
        lowerB = (vMax)*toFrac(rngS[1])
        printfT("Case 3.2",
                "Alice has ≤ $f large-shs",
                "She must also have ≥ $(vMax-f) small-shs, so her possible muffin amount lies in:",
                "",
                "($vMax×$(rngS[1]), $(vMax-f)×$(rngS[2]) + $f×$(rngL[2]))",
                "= ($(formatFrac(lowerB)), $(formatFrac(upperB)))",
                "",
                "Since $size lies in this interval, this case is possible",
                "",
                "Contradicts assumption if α ≥ $alpha")
    end

    # Conclude with alpha's value
    printHeader("CONCLUSION")
    printfT("Compute α",
            "Each possible case derive the same lower bound for α that contradicts the assumption",
            "",
            "All possible cases contradict the assumption iff.",
            "α ≥ $alpha")
    printfT("Conclusion",
            "muffins($m, $s) ≤ α, ∀ α ≥ $alpha",
            "",
            "muffins($m, $s) ≤ $alpha")

    printEnd()
end

end
