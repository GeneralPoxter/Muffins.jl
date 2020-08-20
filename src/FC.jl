module FC

include("Format.jl")
using .Format

export fc

# Determines upper bound alpha with Floor-Ceiling Theorem
# Authors: Antara Hebbar and Jason Liu
function fc(m::Int64, s::Int64; output::Int64 = 1)
    output > 0 && printHeader(center("FLOOR-CEILING THEOREM"))

    if m <= 0 || s <= 0
        if output > 0
            printf("Floor-Ceiling Theorem does not apply", line = true)
            printEnd()
        end
        1 // 1
    elseif m < s
        alpha = m // s * fc(s, m, output = 0)
        if output > 0
            printfT(
                "Floor-Ceiling Theorem",
                "Upper bound α of muffins($m,$s) is $(formatFrac(alpha))",
            )
            printEnd()
        end
        alpha
    else
        alpha = m % s == 0 ? 1 // 1 :
            max(1 // 3, min(m // Int64(ceil(2m / s)s), 1 - m // Int64(floor(2m / s)s)))
        if output > 0
            printfT(
                "Floor-Ceiling Theorem",
                "Upper bound α of muffins($m,$s) is $(formatFrac(alpha))",
            )
            printEnd()
        end
        alpha
    end
end

end
