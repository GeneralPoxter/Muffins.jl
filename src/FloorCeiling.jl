module FloorCeiling

include("Format.jl")
using .Format

export fc

# Determines upper bound with Floor-Ceiling Theorem
function fc(m, s)
    printHeader(center("FLOOR-CEILING THEOREM"))
    if m < s
        printf("Floor-Ceiling Theorem does not apply", line=true)
        printEnd()
        Nothing
    else
        alpha = m % s == 0 ? 1//1 : max(1//3, min( m//Int64(ceil(2m/s)s) , 1 - m//Int64(floor(2m/s)s) )) 
        printfT("Floor-Ceiling Theorem",
                "Upper bound of muffins($m,$s) is $(formatFrac(alpha))")
        printEnd()
        alpha
    end
end

end