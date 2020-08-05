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
        a = s-(3*d*k)
        comden = 3*d*k+a

        if 2*d+1 <= a <= 3*d
            alpha = (d*k+a//3)//(comden)
        elseif a == 2*d
            alpha = fc(m,s)
        elseif 1 <= a <= d
            alpha = (d*k+min(a//2))//(comden)
        elseif d <= a <= 2*d-1
            alpha = (d*k+min((a+d)//4))//(comden)
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
function ebmproof(m, s, alpha)

#finding V and W
V, W, Vnum, Wnum = sv(m,s)
Wshares=W*Wnum
Vshares=V*Vnum
abuddy=1-alpha


#formatting fractions into strings
den = lcm(s, denominator(alpha))
total = m//s
alphaS = formatFrac(alpha, den)
alphaden = formatFrac(alpha, denominator(alpha))
totalS=formatFrac(total, den)
aB=formatFrac(abuddy, den)

d = m-s

i = 0
while 3*d*i < s
    i += 1
end

k = i-1
a = s-(3*d*k)
comden = 3*d*k+a


if V==3 #ebm only works if there are 2-shares

firstparameter = formatFrac(a//3)
case1 = (3*d*k+a+d)//(comden)
case1str = formatFrac(case1)
V_case1 = formatFrac(1//(V+1))
v_conj1 = formatFrac(case1*(1//(V+1)))
total = formatFrac(m//s)



#claim
printHeader("CLAIM:")
printf("There is a ($m, $s) procedure where the smallest piece is ≥ $alphaS.")
printfT("Note", "Let the common denominator $den. Therefore, alpha will be referred to as $alphaden.")

printHeader("DEFINING TERMS FOR EBM ALGORITHM: ")
printfT("Variables", "We will use the following variables for the EBM algorithm (where m=muffins and s=students):", "", "d = m-s = $d", "",
"k is the largest number >= 0 such that 3dk > s. k = $k.", "", "a = s - 3dk = $a")
printfT("Common Terms", "A buddy of ") #finish def of buddy and match

#assumptions
printHeader("ASSUMPTIONS FOR EBM ALGORITHM:")
printfT("Important note", "The proof is conducted using parameter X. Assume that there is a($m, $s) procedure where X ≥ $(firstparameter) so alpha ≥ 1//3.", "",
"Hence, there is a procedure where every muffin is cut into 2 pieces. There are total $(6*d*k + 2*a +2*d) pieces.")


#CASEWORK, checking if V+1 or V-2 cases are impossible
printHeader("CASEWORK:")

if case1*(1//(V+1)) < alpha
    printfT("Case 1", "If Alice gets ≥ $(V+1) shares then some share is ≤ ", "", "$case1str * $V_case1 ≤ $v_conj1, which is < $alphaden", "",
    "Note: the inequality follows X > a//3 > a//4 and k ≥ 1")
end

if (V-2)==1 && (3*d*k+a+d)//(comden) > 1//2
    printfT("Case 2", "If Alice gets $(V-2) share, since each share is ≤ 1/2, she has ", "",
    "≤ 1/2 ≤ $(3*d*k+a+d)/$(comden), which is impossible")
end

printfT("Case 3", "Everyone is a $V or $(V-1) student. Let s_2 & s_3 be the number of 2-students and 3-students. Since there are $(6*d*k + 2*a +2*d) shares: ", "",
"", "$(V)s_$V + $(V-1)s_$(V-1) = $(6*d*k + 2*a +2*d)", "", "s_$V + s_$(V-1) = $(3*d*k +a)", "",
"Hence, s_$(V-1) = $(3*d*k+a-2*d), s_$(V) = $(2*d). So there are $(6*d*k+2*a-4*d) $(V-1) shares and $(6*d) $V-shares.")

printHeader("CONTINUING CASE ANALYSIS/SETTING UP FOR ALGORITHM PROOF")
printfT("Case 3a", "There is a $V-share ≥ ($(d*k+a+d)-2X)/$comden.
The remaining $(V-1) $V-shares add up to ", "", "≤ $m/$s - ($(d*k+a+d)-2X)/$comden = ($(2*d*k)+2X)/$comden.", "", "Hence there is a $V-share ($(2*d*k)+2X)/$comden * 1/2 = ($(d*k)+X)/$comden")
printfT("Case 3b", "There is a $(V-1) share ≥ ($(2*d*k+a)-X)/$comden. Its buddy is ", "", "≤ 1 - ($(2*d*k+a)-X)/$comden  = ($(d*k)+X)/$comden")
printfT("Case 3c", "There is a $(V-1) share ≤ ($(d*k+d)+X)/$comden. Its match is ", "", "≥ $total - ($(d*k+d)+X)/$comden  = ($(2*d*k+a)-X)/$comden",
"", "Its buddy is ≤ 1 - ($(2*d*k+a)-X)/$comden  = ($(d*k)+X)/$comden")
printfT("Case 3d", "There is a $V-share ≤ ($(d*k)+X)/$comden. This case is obvious.")
printfT("Case 3e", "All $V-shares are in (($(d*k)+X)/$comden, ($(d*k+a+d)-2X)/$comden))", "",
"All $(V-1) shares are in (($(d*k+d)+X)/$comden, ($(2*d*k+a)-X)/$comden)")

printHeader("INTERVAL DIAGRAM:")
printf("The following diagram depicts what we know so far: ")
println("\n",
        interval(["(", "($(d*k)+X)/$comden"],
                [")[", "($(d*k+a+d)-2X)/$comden)"],
                ["](", "($(d*k+d)+X)/$comden"],
                [")", "($(2*d*k+a)-X)/$comden"],
                labels=["$(V)s_$V $V-shs", "0", "$(V-1)s_$(V-1) $(V-1)-shs"]))
printf("The assumption that X ≥ $(a//3) ensures that the interval of $V-shares and $(V-1) shares do not intersect.")

#Define bijections
printHeader("BIJECTIONS:")
printfT("Define", "We define the following (where B signifies buddying and M signifies matching):", "", "M₀ = (($(d*k)+X)/$comden, ($(d*k+a+d)-2X)/$comden))",
"B₀ = B(M₀) = (($(2*d*k+a-d)-X)/$comden), ($(2*d*k+a)-X)/$comden)", "", "∀ ≤ i ≤ $(k-1), [Mᵢ = M(Bᵢ₋₁) = (($(d*k)+$(d)i+X)/$comden, $(d*k)+$(d)(i+1)+X)/$comden)]",
"", "∀ ≤ i ≤ $(k-1), [Bᵢ = B(Mᵢ) = (($(2*d*k+a)-$(d)(i-1)-X)/$comden, ($(2*d*k+a)-$(d)(i)-X)/$comden)]")




#using findend function to solve for interval gaps
#((_, x), (y,_)) = findend(m,s,alpha,V)


#defining buddies and matches
#=ybuddy = 1-y
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
printHeader("INTERVAL DIAGRAM: ")=#



#using a buddy-match sequence to find a contradiction


end #if v==3 or 2
end #if proof end
end #function end
