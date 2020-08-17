module HBM

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

include("FC.jl")
using .FC

export hbm, VHBM

# Determines an upper bound using Hard-Buddy Match methon
# Author: Antara Hebbar
function hbm(m::Int64, s::Int64; output::Int64=2)
    output>0&&printHeader(center("HARD-BUDDY MATCH METHOD"))

    if m<s|| m<=0 || s<=0
        if output > 0
            printf("HBM method does not apply", line=true)
            printEnd()
        end
        return 1
    elseif m%s == 0
        if output > 0
            printf("Since $m % $s = 0, f($m, $s) = 1.", line=true)
            printEnd()
        end
        return 1
    else
        V = Int64(ceil(2m/s))
        if V==3
            #important variables for algorithm hbm
            d = m-s
            i = 0
            while 3*d*i < s
                i += 1
            end
            k = i-1
            a = s-(3*d*k)
            Xsolutions = Xsol(a,d,k)

            if length(Xsolutions)==0
                return 1
            elseif a==(2*d)
                alpha = fc(m,s, output=0)
                if output>0
                    printf("Since a=2d, hbm($m, $s) = fc($m, $s). Therefore, upperbound of hbm($m, $s) is $alpha.", line=true)
                    printEnd()
                end
                return alpha
            else
                X=minimum(Xsolutions)

                #special cases
                if a==10&&d==7&&m==(21*k+17)&&s==(21*k+10)
                    alpha=(7*k+4)//(21*k+10)
                elseif a==4&&d==3&&m==(9*k+7)&&s==(9*k+4)
                    alpha=(9*k+5)//(27*k+12)
                else
                    alpha=(d*k+X)//(3*d*k+a)
                end

                if VHBM(a,d,k,X, output=output)
                    if output>0
                        printfT("Deriving alpha", "The derived value for X is $X. f($m, $s) ≤ (dk+X)/(3dk+a).", "",
                        "Once plugging in d, k, a, and X, the upper bound of hbm($m, $s) is $alpha.")
                        printEnd()
                    end
                    return alpha
                else
                    if output>0
                        printf("VHBM does not verify the alpha derived by Hard-Buddy Match.", line=true)
                        printEnd()
                    end
                return 1
                end
            end
        else
            if output>0
                printf("Hard-buddy match method requires that students are given 3-shares and 2-shares.
                Since in f($m, $s), students are given $V and $(V-1) shares, HBM does not apply here.", line=true)
                printEnd()
            end
            return 1
        end
    end
end


#Verifies that with an input of a,d,k,X, f(3dk+a+d, 3dk+a) ≤ (dk+X)/(3dk+a), ouputs proof if wanted
function VHBM(a,d,k,X; output::Int64=2)
    #pre-processing stage: checks for a bad input
    pre=true
    alpha=(d*k+X)//(3*d*k+a)
    muffins = 3*d*k+a+d
    students=3*d*k+a
    V = Int64(ceil(2*muffins/students))
    comden=3*d*k+a

    #formatting
    alphaS=formatFrac(alpha)

    output>1&&printHeader("PREPROCESSING STAGE: ")

    if a==(2*d) #use FC
        alpha=fc(muffins, students)
        if output>1
            printf("Inputs are verified.")
        end
    end


    if X>=a//3 && a>(2*d+1) && a<(3*d-1) #theorem 10.11.1 in muffins book, we assume a is in that interval
        if output>1
            printf("Inputs are verified.")
        end
    end

    if X>=(a//2) #theorem 10.11.2, we assume X<a/2
        if output>1
            printf("Inputs are verified.")
        end
    end
    if X>=(a+d)//4 #theorem 10.11.3, we assume X<(a+d)/4
        if output>1
            printf("Inputs are verified.")
        end
    end

    if a<1 || a>(3*d)
        pre=false
        if output>0
            printf("Bad input, VHBM failed. a ∉ {1...$(3*d)}.")
            printEnd()
        end
        return false
    end

    if X<a//3
        pre=false
        if output>0
            printf("Bad input, VHBM failed. X is less than a/3 ($(a//3)).")
            printEnd()
        end
        return false
    end

    output>1&&printf("END OF PREPROCESSING STAGE.")

    if pre&&V==3

        if output>1 #start of proof
            printHeader("START OF PROOF:")
            printf("Assume, by way of contradiction, there is a ($muffins, $students) procedure where the smallest piece is > $alphaS.", "",
            "We are looking for a contradiction.")
            printLine()

            printfT("Solving for students and shares", "Every student has $(V) or $(V-1) shares.", "", "Let s₂ and s₃ equal the number of 2 and 3-students.",
            "", "s₂ = $(3*d*k+a-2*d). There are $(6*d*k+2*a-4*d) 2-shares.", "", "
            s₃ = $(2*d). There are $(6*d) 3-shares.")

            printHeader("DEFINING TERMS FOR ALGORITHM: ")
            printfT("Variables", "We will use the following variables for the HBM algorithm (where m=muffins and s=students):", "", "d = m-s = $d", "",
            "k is the largest number >= 0 such that 3dk > s. k = $k.", "", "a = s - 3dk = $a")

            printfT("Note", "A buddy of share size x is equal to 1-x. A match of share size y is equal to $muffins/$students-y.")
        end

        #variables for interval diagram
        x = (d*k+a+d-2*X)//(comden)
        y=(d*k+d+X)//comden
        alphabuddy = 1-alpha
        #formatting
        den=denominator(alpha)
        xS, yS, aB =formatFrac(x, den), formatFrac(y, den), formatFrac(alphabuddy)

        bij1, bij2=formatFrac((2*d*k+a-d-X)//comden, den), formatFrac((2*d*k-d+2*X)//comden)
        int1, int2=formatFrac(((d*k+a-X)//comden), den), formatFrac(((d*k+2X)//comden), den)
        int3, int4 = formatFrac((2*d*k+a-2*X)//comden, den), formatFrac((2*d*k+X)//comden, den)
        bound1S=formatFrac((d*k+a-X)//comden, den)
        int5 = formatFrac((d*k+a//2)//comden, den)


            if output>1
                printHeader("INTERVAL DIAGRAM:")
                printf("The following diagram depicts what we know so far: ")
                println("\n",
                interval(["(", "$alphaS"],
                    [")[", "$xS"],
                    ["](", "$yS"],
                    [")", "$aB"],
                    labels=["$(V)s_$V $V-shs", "0", "$(V-1)s_$(V-1) $(V-1)-shs"]))
                printf("The assumption that X ≥ $(a//3) ensures that the interval of $V-shares and $(V-1) shares do not intersect.")
                printLine()


                printfT("Buddy/Match Bijections", "We define the following (where B signifies buddying and M signifies matching):", "", "M₀ = [$xS, $yS]",
                "B₀ = B(M₀) = [$bij1, $bij2]", "", "∀ ≤ i ≤ $(k-1), [Mᵢ = M(Bᵢ₋₁) = [($(d*k+a)+$d(i+1)-2X)/$comden, ($(d*k)+$(d)(i+1)+X)/$comden)]",
                "", "∀ ≤ i ≤ $(k-1), [Bᵢ = B(Mᵢ) = [($(2*d*k+a-X)-$(d)(i+1))/$comden, ($(2*d*k+2*X)-$(d)(i+1))/$comden)]") #printing bijections

                printfT("Note", "Since M₀ is empty, so is the Mᵢ's' and Bᵢ's.",
                "Bκ₋₁ = [$int1, $int2] is also empty. We want this to be in the 3-shares.", "",
                "Therefore, we want $int2 < $(xS). This is true.")

                #formatting issues
                z=2*a+2*d
                printHeader("INTERVAL ANALYSIS CONT.:")
                printf("Let the number of shares in [$alphaS, $bound1S] be 𝑧.")
                printfT("HBM Algorithm", "Algorithm proves through buddy-match bijections that 𝑧 = 2a+2d = $(z).", "",
                "For complete proof, read HBM chapter of Muffins Book (page 176-177).")
                printf("The following picture captures what we know. ")


                printf("3-shares:")
                println("\n",
                interval(["(", "$alphaS"],
                    [")[", "$int1"],
                    ["](", "$int2"],
                    [")[", "$xS"],
                    ["]", "$yS"],
                labels=["$z 3-shs", "0", "$(6*d-z) 3-shs", "0"]))
                println()

                printf("2-shares: ")
                println("\n",
                interval(["(", "$yS"],
                    [")[", "$bij1"],
                    ["]", "$bij2"],
                labels=["$(6*d*k-10*d+2*a) 3-shs", "0"]))
                println("\n",
                interval(["(", "$bij2"],
                    [")[", "$int3"],
                    ["](", "$int4"],
                    [")", "$aB"],
                labels=["$(6*d-z) 2-shs", "0", "$z 2-shs"]))

                printLine()

                casekey, casenum, endsum =k//2, 1, 1
                midpoint = endsum *1//2
                parity, ivalue, method = "even", "k/2", "buddying"

                if k%2!=0
                    casekey, casenum, endsum = (k+1)//2, 2, (3*d*k+a+d)//comden
                    midpoint = endsum* 1//2
                    parity, ivalue, method = "odd", "(k+1)/2", "matching"
                end


                sym1 = formatFrac((d*k+casekey*d+X)//comden, den)
                sym2 = formatFrac((d*k+a+d*casekey-X)//comden, den)

                printHeader("CASES:")
                printfT("Case $casenum", "k ($k) is $parity. Let i = $ivalue = $casekey.", "", "Mᵢ = [$sym1, $sym2].", "",
                "The sum of the endpoints is $endsum, so the midpoint is $midpoint. So, Mκ/2 is symmetric by $method.")

                printf("The following is what we know about the 3-shares: ")
                println("\n",
                interval(["(", "$alphaS"],
                    ["|", "$int5"],
                    [")[", "$int1"],
                    ["](", "$int2"],
                    [")", "$xS"],
                labels=["$(a+d) 3-shs", "$(a+d) 3-shs","0",  "$(4*d-2*a) 3-shs"]))
                printLine()
                printfT("Defining intervals", "We define the following intervals: ", "",
                "|J₁| = [$alphaS, $int5], |J₂| = [$int5, $int1], |J₃| = [$int2, $xS]", "",
                "J₁ = J₂ = $(a+d)      J₃ = $(4*d-2*a)")

            end

    # Determine possible share combinations
    shares = combs(3,3) #not sure if this is necessary
    workingcomb=[]

    for (a, b, c) in comboTup(3, 3)
        NEsum = a*toFrac(int5) + b*toFrac(int1) + c*x
        TMsum = a*alpha + b*toFrac(int5) + c*toFrac(int2)
        if NEsum > muffins//students > TMsum && [a,b,c] in shares
            append!(workingcomb, [(a, b, c)])
        end
    end

    len = length(workingcomb)

    if len>0&&(2,0,1) in workingcomb
        if output>1
            sharecombs = ["$a shares from J1, $b shares in J2, and $c shares in J3" for (a,b,c) in workingcomb]
            printHeader("POSSIBLE SHARES: ")
            printfT("Determining share combos", "Given all possible share combos, the only shares from J1, J2, and J3 that are not forbidden are: ",
            "", sharecombs..., "")
        end

        output > 1 && printHeader("EQUATION ANALYSIS:")
        if len==1
                if output>1
                    printfT("One-variable equation", "Since there is only 1 possible share combination, we look for a 2d solution in following set of equations:",
                    "", "Equation 1 based on |J₁|+ |J₂| = a+d → 2y₁₁₃ = a+d = $(a+d)", "",
                    "Equation 2 based on |J₃| = 4d-2a → y₁₁₃ = 4d-2a = $(4*d-2*a)", "", "Equation 3 based on s₃ = 2d → y₁₁₃ = 2d = $(2*d)", "",
                    "Since y₁₁₃ has a solution from {0...$(2*d)}, VHBM verifies alpha")
                end
            return true

        elseif len==2
            sol=false
            if (1,1,1) in workingcomb
                sol=true
                eq1, eq2, eq3, eq4 = "2y₁₁₃+y₁₂₃", "y₁₂₃", "y₁₁₃+y₁₂₃", "y₁₁₃+y₁₂₃"
            elseif (0,3,0) in workingcomb
                sol=true
                eq1, eq2, eq3, eq4 = "2y₁₁₃", "3y₂₂₂", "y₁₁₃", "y₁₁₃+y₂₂₂"
            end

            if sol
                if output>1
                    printfT("Two-variable equations", "We look for a 2d solution in following set of equations:",
                    "", "Equation 1 based on |J₁|+ |J₂| = a+d → $eq1 = a+d = $(a+d),  $eq2 = a+d = $(a+d)", "",
                    "Equation 2 based on |J₃| = 4d-2a → $eq3 = 4d-2a = $(4*d-2*a)", "", "Equation 3 based on s₃ = 2d → $eq4= 2d = $(2*d)", "",
                    "Since y₁₁₃ has a solution from {0...$(2*d)}, VHBM verifies alpha")
                end
                return true #verified for 2 variable solutions
            else
                if output>1
                    printf("No 2d solution found with derived 2-variable share combinations, vhbm failed.")
                end
                return false
            end
        elseif len==3
            if (1,1,1) in workingcomb&& (1,0,2) in workingcomb
                sol=true
                eq1, eq2, eq3, eq4 = "2y₁₁₃+y₁₂₃", "y₁₂₃", "y₁₁₃+y₁₂₃", "y₁₁₃+y₁₂₃"
            elseif (1,1,1) in workingcomb&& (0,3,0) in workingcomb
                sol=true
                eq1, eq2, eq3, eq4 = "2y₁₁₃", "3y₂₂₂", "y₁₁₃", "y₁₁₃+y₂₂₂"
            elseif (1,2,0) in workingcomb && (0,3,0) in workingcomb
                sol=true
            elseif (1,1,1) in workingcomb&& (0,2,1) in workingcomb
                sol=true
            end

            if sol
                return true
            else
                return false
            end
        elseif len==4
            if (2,1,0) in workingcomb&& (1,2,0) in workingcomb && (0,3,0) in workincomb
                sol=true
                eq1, eq2, eq3, eq4 = "2y₁₁₃+y₁₂₃", "y₁₂₃", "y₁₁₃+y₁₂₃", "y₁₁₃+y₁₂₃"
            elseif (1,2,0) in workingcomb&& (1,1,1) in workingcomb && (0,3,0) in workincomb
                sol=true
                eq1, eq2, eq3, eq4 = "2y₁₁₃", "3y₂₂₂", "y₁₁₃", "y₁₁₃+y₂₂₂"
            elseif (1,1,1) in workingcomb && (1,0,2) in workingcomb && (0,3,0) in workincomb
                sol=true
            elseif (1,1,1) in workingcomb&& (1,0,2) in workingcomb && (0,2,1) in workingcomb
                sol=true
            elseif (1,1,1) in workingcomb&& (0,3,0) in workingcomb && (0,2,1) in workingcomb
                sol=true
            end

            if sol
                return true
            else
                return false
            end
        else
            return false #to be completed
        end


    else
        if output>1
            printf("There are no possible share combinations, vhbm failed")
        end
        return false
    end
    else
        if output>0
            printf("Vhbm failed, hbm method needs students to have $V or $(V-1) shares.")
            printEnd()
        end
    end
end

#using COND function and a,d,k values to derive candidates for X
function Xsol(a,d,k)
    Xsolutions = Array{Rational}(undef, 0)

    if d>=1 && k>=1 && a >= 1 && a <= (2*d) #11.5.1: y₁₁₃ permitted, all other variables forbidden

        X = max((a+2*d)//6, (2*a-d)//3) #corollary 11.7
        if COND(a,d,X)
            append!(Xsolutions, X)
        end

        if a!=1 || d!=1 #11.5.2: y₁₁₃, y₁₂₃ permitted, all others forb
        X=max((a+d)//5, (2*a-d)//3, d//2) #corollary 11.8
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a != (7*d//5) #11.5.3: y₁₁₃, y₂₂₂ permitted, all others forb
        X=max((3*a-2*d)//4, (a+2*d)//6)#corollary 11.9
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a<(7*d//5) || a> (5*d//3) #11.5.4: y₁₁₃, y₁₂₂, y₂₂₂ permitted, all others forb
        X=max(a-d, (a+2*d)//6) #corollary 11.10
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a!=1 || d!=1 #11.5.5: y₁₁₃, y₁₂₃, y₁₃₃ permitted, all others forb
        X=max((2*a-d)//3, d//2) #corollary 11.11
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a<d ||a>(7*d)//5 #11.5.6: y₁₁₃, y₁₂₃, y₂₂₂ permitted, all others forb
        X=max((3*a-2*d)//4, (a+d)//5, d//2) #corollary 11.12
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a!=1 || d!=1 #11.5.7: y₁₁₃, y₁₂₃, y₂₂₃ permitted, all others forb
        X=max((2*a-d)//3, (a+d)//5) #corollarly 11.13
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a<(7*d)//5 #11.5.8: y₁₁₂, y₁₁₃, y₁₂₂, y₂₂₂ permitted, all others forb
        X=(a+2*d)//6 #corollarly 11.14
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if d>a || a> (7*d)//3 #11.5.9: y₁₂₂, y₁₁₃, y₁₂₃, y₂₂₂ permitted, all others forb
        X=max(a-d, (a+d)//5, d//2) #corollarly 11.15
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a<d//2 || a> (7*d)//5 #11.5.10: y₁₃₃, y₁₁₃, y₁₂₃, y₂₂₂ permitted, all others forb
        X=max((3*a-2*d)//4, d//2) #corollarly 11.16
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a<d//2 || a> (7*d)//5 #11.5.11: y₁₃₃, y₁₁₃, y₁₂₃, y₂₂₃ permitted, all others forb
        X=max((2*a-d)//3, (a+2*d)//8) #corollarly 11.17
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end

        if a<d || a> (7*d)//5 #11.5.12: y₁₁₃, y₁₂₃, y₂₂₂, y₂₂₃ permitted, all others forb
        X=max((a+d)//5, (3*a-2*d)//4) #corollarly 11.17
            if COND(a,d,X)
                append!(Xsolutions, X)
            end
        end
    end

    return Xsolutions

    #else
        #A = Array{Int64}(undef, 0)
        #return A
    #end
end

#Helper function for Xsol, determines if generated X meets specified condition
function COND(a,d,X)
    if a//3<=X&& X < min(a//2, (a+d)//4)
        return true
    else
        return false
    end
end

#Helper function for VHBM,  returns all permutations from 0 to targ that sum to targ of size n
function combs(targ::Any,n::Any)

openvec = Vector{Int64}(undef, 0)
if n==0 #if length is 0, return empty vector
    return openvec
else

sol = Vector{Int64}(undef, 0)
fullsol = Vector{Vector{Int64}}(undef, 0)


for i = 0:targ
    push!(sol, i)
end

fullsol = reverse.(digits.(0:targ^n-1,base=targ,pad=n))
len=length(fullsol)

finalsol = Array{Array{Int64,1}}(undef, 0)

for i = 1:len
    element = fullsol[i]
    if sum(element)==targ
        push!(finalsol, element)
    end
end
othersolutions = Array{Array{Int64}}(undef, 0)

othersolutions = targperm(targ, n)

splitting(x, n) = [x[i:min(i+n-1,length(x))] for i in 1:n:length(x)] #function will split targperm output into increments of length n

append!(finalsol, splitting(othersolutions, n))



end
end


#Helper function for combs, retuns permuations of target number and 0
function targperm(targ, n)

littlesol = Array{Int64, 1}(undef, 0)
zero = Array{Int64, 1}(undef, 0)
bigsol = Array{Array{Int64, 1}}(undef, 0)
answer = Array{Int64, 1}(undef, 0)

for i = 1:n
    push!(zero, 0)
    push!(bigsol, zero) #generates n arrays consisting of zeros
end


#combinations of 0 and target number
index = 1
for i = 1:n
    littlesol = bigsol[i];
    for j = 1:n
        if index == j
            littlesol[j] =targ
            append!(answer, littlesol[j])
        else
            littlesol[j]=0
            append!(answer, littlesol[j])
        end
    end
    index+=1

end

return answer


end

end
