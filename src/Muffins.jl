module Muffins

include("FloorCeiling.jl")
using .FloorCeiling

include("Half.jl")
using .Half

include("FindProc.jl")
using .FindProc

include("Matrix.jl")
using .Matrix

export muffins

# Solves muffin problem for m muffins and s students -- Work in progress 
function muffins(m, s)
    # TODO -- add case where m < s
    alpha = min(fc(m, s), half(m, s))
    findproc(m, s, alpha)
end

end