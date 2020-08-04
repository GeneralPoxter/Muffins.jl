module EBM

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

include("FC.jl")
using .FC

export ebm

# Determines upper boudn alpha with Easy Buddy Match, optionally outputs proof
# Author: Antara Hebbar
function ebm(m::Int64, s::Int64; output::Int64=2)
    output > 0 && printHeader(center("EASY BUDDY MATCH"))

    if m < s
        if output > 0
            printf("Easy Buddy Match does not apply", line=true)
            printEnd()
        end
        return Nothing
    elseif m % s == 0
        if output > 0
            printfT("Easy Buddy Match",
                    "Since $m % $s = 0, muffins($m,$s) = 1")
            printEnd()
        end
        return 1
    end

    (V, W, sV, sW) = sv(m, s)
    numV = (V)sV
    numW = (W)sW

    alpha = 1
    if V == 3
        d = m-s

        i = 0
        while 3*d*i < s
            i += 1
        end

        k = i-1
        j = s-(3*d*k)

        if 2*d+1 <= j <= 3*d
            alpha = (d*k+j//3)//(3*d*k+j)
        elseif j == 2*d
            alpha = fc(m,s)
        elseif 1 <= j <= d
            alpha = (d*k+min(j//2))//(3*d*k+j)
        elseif d <= j <= 2*d-1
            alpha = (d*k+min((j+d)//4))//(3*d*k+j)
        end

        if output > 0 && alpha != 1
            if output == 2
                ebmproof(m, s, alpha)
            else
                printfT("Easy Buddy Match",
                        "Upper bound of muffins($m,$s) is $(formatFrac(alpha))")
                printEnd()
            end
        end
        return alpha
    end

    if output > 0
        printf("Easy Buddy Match inconclusive", line=true)
        printEnd()
    end
    alpha
end

# Work in progress
# Output proof of Easy Buddy Match
function ebmproof(m, s, a, proof::Bool=true)

#finding V and W
V, W, Vnum, Wnum = sv(m,s)
Wshares=W*Wnum
Vshares=V*Vnum
abuddy=1-a


#formatting fractions into strings
den = lcm(s, denominator(a))
total = m//s
aS = formatFrac(a, den)
alpha = formatFrac(a, denominator(a))
totalS=formatFrac(total, den)
aB=formatFrac(abuddy, den)


if proof

if V==3 #ebm only works if there are 2-shares

#claim
printHeader("CLAIM:")
printf("There is a ($m, $s) procedure where the smallest piece is ≥ $alpha.")
printfT("Note", "Let the common denominator $den. Therefore, alpha will be referred to as $aS.")

#assumptions
printHeader("ASSUMPTIONS:")
printfT("Determining muffin pieces", "If there is an ($m, $s) procedure with smallest piece α > 1/3, there is an ($m, $s) procedure where every muffin is cut into 2 pieces. Hence, there are $(2*m) shares.")
printfT("Buddies", "If there exists share size α, there also must exist a share size 1-α. All possible shares sizes exist between [$aS, $aB].")

#solving for shares
printHeader("SOLVING FOR # OF SHARES:")
printf("Each student will get either $V or $W shares.")
printLine()
printfT("Determining sharesizes", "While s_$V is the number of $V-shares and s_$W is the number of $W-shares: ","", "($V)s_$V + ($W)s_$W = $(2*m)  (total shares) ", "s_$V + s_$W = $s  (total students)", "", "$Vnum students get $V pieces and $Wnum students get $W pieces. There are $Vshares $V-shares and $Wshares $W-shares.")
println("")

#using findend function to solve for interval gaps
((_, x), (y,_)) = findend(m,s,a,V)


#defining buddies and matches
xbuddy = 1-x
ybuddy = 1-y
xmatch = total-x
ymatch = total-y

#formatting intervals
xS=formatFrac(x, den)
yS=formatFrac(y, den)
xB=formatFrac(xbuddy, den)
yB=formatFrac(ybuddy, den)
xM=formatFrac(xmatch, den)
yM=formatFrac(ymatch, den)

#interval graph
printHeader("INTERVAL DIAGRAM: ")
printf("The following diagram depicts what we know so far: ")
println("\n",
        interval(["(", aS],
                [")[", xS],
                ["](", yS],
                [")", aB],
                labels=["$Vshares $V-shs", "0", "$Wshares $W-shs"]))


#using a buddy-match sequence to find a contradiction


end #if v==3 or 2
end #if proof end
end #function end

end