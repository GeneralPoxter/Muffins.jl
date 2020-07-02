module FloorCeiling

export fc

# Determines upper bound with Floor-Ceiling Theorem
function fc(m, s)
    if m < s
        "fc does not apply"
    else
        m % s == 0 ? 1 : max(1//3, min( m//Int64(ceil(2m/s)s) , 1 - m//Int64(floor(2m/s)s) )) 
    end
end

end