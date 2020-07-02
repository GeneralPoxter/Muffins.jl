module Muffins

include("FloorCeiling.jl")
using .FloorCeiling

include("FindProc.jl")
using .FindProc

include("Matrix.jl")
using .Matrix

export muffins

# Solves muffin problem for m muffins and s students -- Work in progress 
function muffins(m, s)
    # TODO -- add case where m < s
    alpha = fc(m, s)
    println("Upper bound is: ", alpha, " by Floor-Ceiling Theorem")
    findproc(m, s, alpha)
end

end