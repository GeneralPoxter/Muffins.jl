module Half

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

export half, vhalf

# Determines upper bound with Half Method, optionally outputs proof
function half(m::Int64, s::Int64, proof::Bool=true)
    printHeader(center("HALF METHOD"))

    if m < s
        printf("Half Method does not apply", line=true)
        printEnd()
        return Nothing
    elseif m % s == 0
        printfT("Half Method",
                "Since $m % $s = 0, muffins($m,$s) = 1")
        printEnd()
        return 1
    end

    (V, W, sV, sW) = sv(m, s)
    numV = (V)sV
    numW = (W)sW

    # Derive alpha using Half Algorithm
    if numW > numV
        alpha = 1 - (m//s-1//2)//(V-2)          # Value for alpha derived by solving y = 1/2
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vhalf(m, s, alpha, proof)
            return alpha
        end
    elseif numW < numV
        alpha = (m//s-1//2)//(V-1)              # Value for alpha derived by solving x = 1/2
        alpha = alpha < 1/3 ? 1//3 : alpha
        if vhalf(m, s, alpha, proof)
            return alpha
        end
    end

    printf("V-Conjecture inconclusive, Half Method inconclusive", line=true)
    printEnd()
    1
end

# Helper function for half -- verifies whether half(m, s, alpha) is conclusive
function vhalf(m::Int64, s::Int64, alpha::Rational{Int64}, proof::Bool=true)
    if m < s || m % s == 0
        printf("VHalf does not apply", line=true)
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

        # Initialize Half Method proof
        if proof
            # Define and format variables for proof
            alphaF = formatFrac(alpha)
            size = formatFrac(m//s)
            a = formatFrac(m//(V+1)s)
            b = max(1-m//(W-1)s, 0)
            b1 = formatFrac(1-b)
            b = formatFrac(b)

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
                    "Since each muffin is cut into 2 shs that are buddies, the # of shs ≤ 1/2 must equal the # of shs ≥ 1/2",
                    "It follows that the # of shs ≤ 1/2 and the # of shs ≥ 1/2 cannot exceed $m")

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
        if m//s * 1//(V+1) > alpha || 1 - m//s * 1//(V-2) > alpha
            printf("V-Conjecture does not apply, VHalf failed", line=true)
            return false
        end

        ((_, x), (y, _)) = findend(m, s, alpha, V)

        # Check if V-Conjecture works
        if (m//s-x) * 1//(V-1) != alpha || 1 - (m//s-y) * 1//(W-1) != alpha
            printf("V-Conjecture inconclusive, VHalf failed", line=true)
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
            c = formatFrac(m//s-x, cd)
            d = formatFrac(m//s-y, cd)
            xF = formatFrac(x, cd)
            yF = formatFrac(y, cd)

            # Continue casework
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
                    "Alice has a $V-sh ≥ $xF",
                    "Her other $(V-1) $V-shs sum to ≤ ($size - $xF) = $c",
                    "One of them is ≤ ($c × 1/$(V-1)) = $alphaF",
                    "",
                    "Contradicts assumption if α ≥ $alphaF")

            printfT("Case 4",
                    "Bob has a $W-sh ≤ $yF",
                    "His other $(W-1) $W-shs sum to ≥ ($size - $yF) = $d",
                    "One of them is ≥ ($d × 1/$(W-1)) = $alpha1",
                    "Its buddy is ≤ (1 - $alpha1) = $alphaF",
                    "",
                    "Contradicts assumption if α ≥ $alphaF")

            println()
            printf("The following intervals capture the negation of the previous cases:")
            if x <= y && xF > alphaF && yF < alpha1
                println("\n",
                        interval(["(", alphaF],
                                [")[", xF],
                                ["](", yF],
                                [")", alpha1],
                                labels=["$numV $V-shs", "0", "$numW $W-shs"]))
            elseif xF == alphaF && yF == alpha1
                println("\n",
                        center("There is no conclusive negation"))
                printfT("Case 5",
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
            end
        end

        # Conclude Case 5 (interval case)
        half = formatFrac(1//2, cd)
        if x <= 1/2 && numV > m
            if proof && genInt
                printfT("Case 5",
                        "This case is impossible because there are more than $m shares ≤ $half, which violates the Property of Buddies")
            end
        elseif y >= 1/2 && numW > m
            if proof && genInt
                printfT("Case 5",
                        "This case is impossible because there are more than $m shares ≥ $half, which violates the Property of Buddies")
            end
        elseif genInt
            # Fail if intervals inconclusive
            if proof
                printfT("Case 5",
                        "The Half Method is inconclusive on these intervals, VHalf failed")
            else
                printf("Could not generate conclusive intervals, VHalf failed", line=true)
            end
            return false
        end

        # Conclude proof
        alpha = formatFrac(alpha)
        if proof
            # Conclude with alpha's value
            printHeader("CONCLUSION")
            printfT("Compute α",
                    "Each possible case derives a lower bound for α that contradicts the assumption",
                    "",
                    "All possible cases contradict the assumption iff.",
                    "α ≥ max($a, $b, $alpha) = $alpha")
            printfT("Conclusion",
                    "muffins($m,$s) ≤ α, ∀ α ≥ $alpha",
                    "",
                    "muffins($m,$s) ≤ $alpha")
        else
            printfT("Half Method",
                    "Upper bound of muffins($m,$s) is $alpha")
        end
        printEnd()

        true
    end
end

end
