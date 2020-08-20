module Muffins

include("FC.jl")
using .FC

include("Half.jl")
using .Half

include("Int.jl")
using .Int

include("Mid.jl")
using .Mid

include("EBM.jl")
using .EBM

include("HBM.jl")
using .HBM

include("Gap.jl")
using .Gap

include("FindProc.jl")
using .FindProc

include("Matrix.jl")
using .Matrix

export muffins

# Solves muffin problem for m muffins and s students -- Work in progress
# Authors: Antara Hebbar and Jason Liu
function muffins(m::Int64, s::Int64; output::Int64=1)
    alphas = [  fc(m, s, output=0),
                half(m, s, output=0),
                int(m, s, output=0),
                mid(m, s, output=0),
                ebm(m, s, output=0),
                hbm(m, s, output=0),
                gap(m, s, output=0)]
    alpha = minimum(alphas)
    disp = output > 0

    method = ""
    if alpha == alphas[1]
        fc(m, s, output=output)
        method = "Floor-Ceiling Theorem"
    elseif alpha == alphas[2]
        half(m, s, output=output)
        method = "Half Method"
    elseif alpha == alphas[3]
        int(m, s, output=output)
        method = "Interval Method"
    elseif alpha == alphas[4]
        mid(m, s, output=output)
        method = "Midpoint Method"
    elseif alpha == alphas[5]
        ebm(m, s, output=output)
        method = "Easy Buddy Match"
    elseif alpha == alphas[6]
        hbm(m, s, output=output)
        method = "Hard Buddy Match"
    else
        gap(m, s, output=output)
        method = "Gap Method"
    end
    disp && println("\nOptimal α derived by $method ⮥")

    procedures = findproc(m, s, alpha, output=0)[2]
    if procedures == Nothing
        disp && println("\nFindProc could not confirm optimal α to be a lower bound\nmuffins($m,$s) failed")
        return 1//1
    end

    #findproc(m, s, alpha, output=output)
    disp && println("\nFindProc found optimal α to be a lower bound as well ⮥")
    disp && println("\nmuffins($m,$s) = $(numerator(alpha))/$(denominator(alpha))")
    alpha
end

end
