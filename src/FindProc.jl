module FindProc

include("Format.jl")
using .Format

export findproc

B = []
memo = Dict()

# Determines procedure with minimum piece size alpha -- Work in progress
function findproc(m::Int64, s::Int64, alpha::Rational{Int64})
    # Clear globals
    global B = []
    global memo = Dict()

    c = numerator(alpha)
    d = denominator(alpha)
    b = lcm(s, d)

    a = Int64(b * c / d)
    B = [x for x in a:(b-a)]

    # Determine vector sets
    L = b - 2a + 1
    V = Int64(ceil(2m/s))
    T = Int64(b * m / s)
    M = vectorize(f(L, b, 2))
    S = vectorize(union( f(L, T, V), f(L, T, V-1) ))

    println("M = ", M)
    println("S = ", S)
end

# Helper function for findproc -- "vectorizes" arrays in set S based on B
function vectorize(S)
    S == Nothing ? Nothing : Set([[count(i->(i==x), s) for x in B] for s in S])
end 

# Helper function for findproc -- "recursively" determines k-size subsets of B[1:i] that sum to T
function f(i, T, k)
    # Base cases
    if i >= 1 && T == 0 && k == 0
        Set()
    elseif T == 0 && k >= 1
        Nothing
    elseif i == 0 && T >= 1
        Nothing
    elseif T >= 1 && k == 0
        Nothing
    elseif T <= -1
        Nothing
    elseif i == 1
        T == k * B[1] ? Set([repeat([B[1]], k)]) : Nothing
    elseif i >= 1 && k == 1
        index = findall(x->x==T, B[1:i])
        length(index) > 0 ? Set([[B[index[1]]]]) : Nothing
    # Recursive case with memoization
    else
        if haskey(memo, (i, T, k))
            get(memo, (i, T, k), 0)
        else
            set = unionF( f(i-1, T, k), mapCat(f(i, T-B[i], k-1), [B[i]]) )
            get!(memo, (i, T, k), set)
        end
    end
end

# Helper function for f -- set unions with Nothing
function unionF(x, y)
    if x == Nothing && y == Nothing
        Nothing
    elseif x == Nothing
        y
    elseif y == Nothing
        x
    else
        union(x, y)
    end
end

# Helper function for f -- concatenate e with each element in set S
function mapCat(S, e)
    S == Nothing ? Nothing : Set([vcat(s, e) for s in S])
end

end