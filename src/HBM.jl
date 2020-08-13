module HBM

include("Computation.jl")
using .Computation

include("Format.jl")
using .Format

include("FC.jl")
using .FC

export hbm, VHBM, COND, Xsol
#=special cases in the book: If a = 10 and d = 7 (note that a 6= 7d
5 ) then f(21k+17; 21k+
10)  7k+4
21k+10: Plug in k = 2 to get f(59; 52)  18
52 , which is
Theorem 11.2.
If a = 4 and d = 3 then f(9k + 7; 9k + 4)  9k+5
27k+12. Plug in
k = 2 to get f(25; 22)  23
66 .=#

#Determines an upper bound using Hard-Buddy Match methon
#Author: Antara Hebbar
function hbm(m::Int64, s::Int64, output::Int64=0)


if m<s||m<=0||s<=0
    if output>1
        printf("HBM method does not apply", line=true)
        printEnd()
    end
    return Nothing
elseif m%s==0
    if output>1
        printf("Since $m % $s = 0, f($m, $s) = 1")
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
else

X=minimum(Xsolutions)
alpha = (d*k+X)//(3*d*k+a)
return alpha
end

else
    if output>0
        printf("Hard-buddy match method requires that students are given 3-shares.
        Since in f($m, $s), students are given $V shares, HBM does not apply here.")
    end
    return 1
end

end

end


#Verifies that with an input of a,d,k,X, f(3dk+a+d, 3dk+a) ≤ (dk+X)/(3dk+a)
function VHBM(X,a,d,k)

#pre-processing stage: checks for a bad input

pre=false
if a<1 || a>(3*d)
    return false
elseif a==(2*d) #use FC
    pre=true
elseif X<a//3
    return false
elseif X>=a//3 && a>(2*d+1) && a<(3*d-1) #theorem 10.11.1 in muffins book,
    pre=true #now we assume that a is in that interval
elseif X>=(a//2) #theorem 10.11.2, we assume X<a/2
    pre=true
elseif X>=(a+d)//4 #theorem 10.11.3, we assume X<(a+d)/4
    pre=true
end
end


#using COND function and a,d,k values to derive candidates for X

function Xsol(a,d,k)
Xsolutions = Array{Rational}(undef, 0)

#if pre

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



#Determining if generated X meets condition for vhbm
function COND(a,d,X)

if a//3<=X&& X < min(a//2, (a+d)//4)
    return true
else
    return false
end
end
end
