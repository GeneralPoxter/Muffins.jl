module Muffins

include("FloorCeiling.jl")
using .FloorCeiling

include("Half.jl")
using .Half

include("Int.jl")
using .Int

include("FindProc.jl")
using .FindProc

include("Matrix.jl")
using .Matrix

export muffins

# Solves muffin problem for m muffins and s students -- Work in progress 
function muffins(m::Int64, s::Int64)
    # TODO -- add case where m < s
    alpha = min(fc(m, s), half(m, s), int(m, s))
    findproc(m, s, alpha)
end

end
