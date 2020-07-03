module Half

include("Format.jl")
using .Format

export half

# Determines upper bound with Half Method, optionally outputs proof
function half(m, s, proof=true)
    printHeader(center("HALF METHOD"))

    if m < s
        printf("Half Method does not apply")
        printEnd()
        return Nothing
    elseif m % s == 0
        printfT("Half Method",
                "Since $m % $s = 0, muffins($m,$s) = 1")
        printEnd()
        return 1
    end

    (V, W, sV, sW) = sv(m, s)

    # Derive alpha using Half Algorithm
    alpha = 1
    if (W)sW > (V)sV
        alpha = 1 - (m//s-1//2)//(V-2)
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vhalf(m, s, alpha)
            return output(m, s, alpha, proof)
        end
    elseif (W)sW < (V)sV
        alpha = (m//s-1//2)//(V-1)
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vhalf(m, s, alpha)
            return output(m, s, alpha, proof)
        end
    end

    printf("Half Method was inconclusive")
    printEnd()
    alpha
end

# Helper function for half -- outputs Half Method conclusion
function output(m, s, alpha, proof)
    if proof
        halfproof(m, s, alpha)
    else
        printfT("Half Method",
                "Upper bound of muffins($m,$s) is $(formatFrac(alpha))")
        printEnd()
    end
    return alpha
end

# Helper function for half -- determines whether half(m, s, alpha) is conclusive
function vhalf(m, s, alpha)
    if alpha < 1/3
        false
    else
        (V, W, sV, sW) = sv(m, s)

        if m//s * 1//(V+1) > alpha || 1 - m//s * 1//(V-2) > alpha
            false
        end

        ((_, x), (y, _)) = findend(m, s, alpha, V)

        if x <= 1/2 && (V)sV > m
            true
        elseif y >= 1/2 && (W)sW > m
            true
        else
            false
        end
    end
end

# Helper function for half -- determines V, V -1 (abbreviated as W), s_V, and s_W
function sv(m, s)
    # Apply V-Conjecture
    V = Int64(ceil(2m/s))
    W = V-1
    sV = (-W)s + 2m
    sW = (V)s - 2m
    (V, W, sV, sW)
end

# Helper function for half -- determines the segments of the interval for the last case
function findend(m, s, alpha, V)
    y = m//s - (1-alpha)*(V-2)
    y = y >= 1-alpha ? 1-alpha : (y <= alpha ? alpha : y)

    x = m//s - alpha*(V-1)
    x = x <= alpha ? alpha : (x >= 1-alpha ? 1-alpha : x)

    ((alpha, x), (y, 1-alpha))
end

# Helper function for half -- generates proof of Half Method
function halfproof(m, s, alpha)
    # Define and format variables for proof
    (V, W, sV, sW) = sv(m, s)
    numV = (V)sV
    numW = (W)sW
    ((_, x), (y, alpha1)) = findend(m, s, alpha, V)
    size = formatFrac(m//s)
    alpha = formatFrac(alpha)
    alpha1 = formatFrac(alpha1)
    a = formatFrac(m//(V+1)s)
    b = formatFrac(max(1-m//(W-1)s, 0))
    c = formatFrac(m//s-x)
    d = formatFrac(m//s-y)
    xF = formatFrac(x)
    yF = formatFrac(y)

    # Establish assumptions and premises
    printHeader("OVERVIEW")
    printfT("Goal", 
            "Prove:",
            "muffins($m,$s) <= alpha = $alpha",
            "by contradicting the assumption")
    printfT("Assumption", 
            "Assume:",
            "The desired upper bound is alpha",
            "muffins($m,$s) > alpha >= 1/3")
    printfT("Theorem 2.6.2", 
            "Since muffins($m,$s) > 1/3, each muffin must be cut into 2 shs, totaling $(2m) shs")
    printfT("Property of Buddies",
            "Since each muffin is cut into 2 shs that are buddies, the # of shs < 1/2 must equal the # of shs > 1/2",
            "It follows that the # of shs < 1/2 and the # of shs > 1/2 cannot exceed $m")

    # Describe case work
    printHeader("CASEWORK")

    printfT("Case 1",
            "If Alice has >= $(V+1) shs, then one of them is <= ($size x 1/$(V+1)) = $a",
            "",
            "Contradicts assumption if alpha >= $a")

    if W-1 <= 1 && m/s > 1
        printfT("Case 2",
                "Bob cannot have <= $(W-1) shs since $size > 1, so this case is impossible")
    else
        printfT("Case 2",
                "If Bob has <= $(W-1) shs, then one of them is >= ($size x 1/$(W-1))",
                "Its buddy is <= (1 - $size x 1/$(W-1)) = $b",
                "",
                "Contradicts assumption if alpha >= $b")
    end

    printfT("Note",
            "The remaining cases deal with everyone having either $W or $V shs, so:",
            "",
            "$(W)s_$W + $(V)s_$V = $(2m)  (total shs)",
            "s_$W + s_$V = $s  (total students)",
            "where s_N = # of students with N shs",
            "",
            "The solution to the system is:",
            "s_$W = $sW, s_$V = $sV",
            "So there are $numW $W-shs and $numV $V-shs")

    printfT("Case 3",
            "If Alice has a $V-sh >= $xF, then her other $(V-1) $V-shs sum to <= ($size - $xF) = $c",
            "One of them is <= ($c x 1/$(V-1)) = $alpha",
            "",
            "Contradicts assumption if alpha >= $alpha")

    printfT("Case 4",
            "If Bob has a $W-sh <= $yF, then his other $(W-1) $W-shs sum to >= ($size - $yF) = $d",
            "One of them is >= ($d x 1/$(W-1)) = $alpha1",
            "Its buddy is <= (1 - $alpha1) = $alpha",
            "",
            "Contradicts assumption if alpha >= $alpha")

    println()
    printf("The following intervals capture the negation of the previous cases:")
    if x <= y && xF != alpha && yF != alpha1
        println("\n",
                interval(["(", alpha],
                        [")[", xF],
                        ["](", yF],
                        [")", alpha1],
                        labels=["$numV $V-shs", "0", "$numW $W-shs"]))
    else
        if xF != alpha
            println("\n",
                    interval(["(", alpha],
                            [")[", xF],
                            [")", alpha1],
                            labels=["$numV $V-shs", "0 $V-shs"]))
        end
        if yF != alpha1
            println("\n",
                    interval(["(", alpha],
                            ["](", yF],
                            [")", alpha1],
                            labels=["0 $W-shs", "$numW $W-shs"]))
        end
    end
    printfT("Case 5",
            "This case is impossible because it violates the Property of Buddies")
    
    # Conclude with alpha's value
    printHeader("CONCLUSION")
    printfT("Compute alpha",
            "Each possible case derives a lower bound for alpha that contradicts the assumption",
            "",
            "All possible cases contradict the assumption iff.",
            "alpha >= max($a, $b, $alpha) = $alpha")
    printfT("Conclusion",
            "Therefore, muffins($m, $s) <= alpha for all alpha >= $alpha",
            "",
            "muffins($m, $s) <= $alpha")

    printEnd()
end

end