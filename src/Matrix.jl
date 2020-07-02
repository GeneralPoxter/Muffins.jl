module Matrix

using JuMP
using Cbc

include("FloorCeiling.jl")
using .FloorCeiling

export solve 

# Matrix method solver -- uses CBC MIP optimizer
function solve(m, s)
    model = Model(Cbc.Optimizer)
    set_optimizer_attribute(model, "allowableGap", 1e-5)
    set_optimizer_attribute(model, "cuts", "off")

    @variable(model, 0 <= x[i=1:m, j=1:s] <= 1)
    @variable(model, 0 <= y[i=1:m, j=1:s] <= 1, Int)
    @variable(model, 1/3 <= z <= fc(m, s), start = fc(m, s))

    @objective(model, Max, z)

    for i=1:m, j=1:s
        @constraint(model, x[i, j] + y[i, j] <= 1)
        @constraint(model, x[i, j] + y[i, j] >= 1/s)
        @constraint(model, z <= x[i, j] + y[i, j])
    end

    for i=1:m
        @constraint(model, sum(x[i, :]) == 1)
    end

    for j=1:s
        @constraint(model, sum(x[:, j]) == m/s)
    end

    optimize!(model)

    println("z = ", rationalize(value(z), tol=1e-8))
end

end