module Muffins

include("FloorCeiling.jl")
using .FloorCeiling

include("Half.jl")
using .Half

include("Int.jl")
using .Int

include("Mid.jl")
using .Mid

#include("FindProc.jl")
#using .FindProc

#include("Matrix.jl")
#using .Matrix

export muffins

# Solves muffin problem for m muffins and s students -- Work in progress 
function muffins(m::Int64, s::Int64; output::Int64=1)
    # TODO -- add case where m < s
    alpha = min(fc(m, s, output=output), half(m, s, output=output), int(m, s, output=output), mid(m, s, output=output))
    #findproc(m, s, alpha, output=output)
    alpha
end

end
