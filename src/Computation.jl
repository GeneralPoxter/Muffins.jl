module Computation

export sv, findend, combo, comboTup

# Determines V, V -1 (abbreviated as W), s_V, and s_W using V-Conjecture
function sv(m, s)
    V = Int64(ceil(2m/s))
    W = V-1
    sV = (-W)s + 2m
    sW = (V)s - 2m
    (V, W, sV, sW)
end

# Determines the segments of the interval in which lie the V- and W-shares
function findend(m, s, alpha, V)
    x = m//s - alpha*(V-1)
    x = x <= alpha ? alpha : (x >= 1-alpha ? 1-alpha : x)
    
    y = m//s - (1-alpha)*(V-2)
    y = y >= 1-alpha ? 1-alpha : (y <= alpha ? alpha : y)

    ((alpha, x), (y, 1-alpha))
end

# Determines all non-negative integer combinations of size k that sum to T
function combo(T, k)
    if k == 0
        return [[]]
    elseif k == 1
        return [[T]]
    elseif T == 0
        return [repeat([0], k)]
    else
        return hcat([vcat.([i], combo(T-i, k-1)) for i=0:T]...)
    end
end

# Converts the results of combo(T, k) into tuples
function comboTup(T, k)
    return [tuple(x...) for x in combo(T, k)]
end

end