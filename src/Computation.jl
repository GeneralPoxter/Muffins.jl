module Computation

export sv, findend, combo, comboTup, intCombo

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

# Given possible combinations of small and large shs (posCombo), determines all possible interval combinations in bounds
function intCombo(m, s, vMax, bounds, smallBounds, posCombo)
    posInt = []
    for tup in comboTup(vMax, length(bounds))
        upperB = sum(tup.*(getindex.(bounds, 2)))
        lowerB = sum(tup.*(getindex.(bounds, 1)))
        numSmall = 0
        for i=1:length(bounds)
            if smallBounds[1] <= bounds[i][1] <= bounds[i][2] <= smallBounds[2]
                numSmall += tup[i]
            end
        end
        if numSmall in posCombo && upperB > m//s > lowerB
            append!(posInt, [tup])
        end
    end
    return posInt
end

end