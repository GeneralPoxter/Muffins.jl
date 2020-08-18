module Format

using TextWrap

export printf, printfT, printHeader, printEnd, printLine, formatFrac, toFrac, interval, center

LEFT_WIDTH = 45
RIGHT_WIDTH = 25
LINE_WIDTH = LEFT_WIDTH + RIGHT_WIDTH

# Formats and outputs a line of text
function printf(text...; line=false)
    line && println()
    println_wrapped(text..., width=LINE_WIDTH)
    line && printLine()
end

# Formats and outputs a line of text with a theorem reference
function printfT(theorem, text...)
    wrapped = join(map(line->wrap(string(line), width=LEFT_WIDTH, break_on_hyphens=false), [text...]), "\n")
    lastPos = occursin("\n", wrapped) ? findlast('\n', wrapped) : 0
    println()
    print(rpad(wrapped, lastPos + LEFT_WIDTH))
    println(lpad(theorem, RIGHT_WIDTH))
    printLine()
end

# Formats and outputs text as a section header
function printHeader(text...)
    println("\n")
    println(text...)
    printLine()
end

# Outputs the end of a procedure
function printEnd()
    println()
    println(center("END"))
end

# Outputs a section separator
function printLine()
    println('—' ^ LINE_WIDTH)
end

# Formats a Rational type variable into its string representation
function formatFrac(frac::Rational{Int64}, den=denominator(frac))
    (n, d) = (numerator(frac), denominator(frac))
    if n % d == 0 && den == d
        return string(Int64(n/d))
    end
    m = den % d == 0 ? Int64(den/d) : 1
    string(m * n, "/", m * d)
end

# Converts a string representation into a Rational type variable
function toFrac(frac::String)
    try
        f = vcat(map(x->parse(Int64, x), split(frac, "/")), [1])
        f[1]//f[2]
    catch e
        Int64(frac)
    end
end

# Outpus a string interval that concatenates given ranges labeled with given labels
function interval(rngs...; labels=repeat([" "], length(rngs) - 1))
    int = ""
    val = ""
    w = maximum(length(rng[2]) for rng in rngs) + 1
    for i in 1:(2length(rngs) - 1)
        if i % 2 == 0
            label = labels[Int64(i/2)]
            int *= label
            val *= ' ' ^ length(label)
        else
            rng = rngs[Int64(ceil(i/2))]
            int *= center(rng[1], width=w)
            val *= center(rng[2], width=w)
        end
    end
    if length(int) > LINE_WIDTH
        lines = []
        i = 0
        while (i)LINE_WIDTH <= length(int)
            append!(lines, [int[(i)LINE_WIDTH+1:min((i+1)LINE_WIDTH, length(int))],
                            val[(i)LINE_WIDTH+1:min((i+1)LINE_WIDTH, length(val))],
                            ""])
            i += 1
        end
        join(lines[1:length(lines)-1], "\n")
    else
        center(int, val)
    end
end

# Centers text within width spaces
function center(text...; width::Int64 = LINE_WIDTH)
    out = []
    half = Int64(floor(width/2))
    for line in text
        mid = Int64(floor(length(line)/2))
        append!(out, [lpad(line[1:mid], half) * rpad(line[(mid+1):length(line)], width-half)])
    end
    join(out, "\n")
end

# Helper function for printfT -- Unicode-compatible version of built-in findlast
function findlast(char::Char, str::String)
    o = 0
    e = 1
    i = 1
    while i <= length(str)
        if str[e] == char
            o = i
        end
        e += nextind(string(str[e]), 1) - 1
        i += 1
    end
    o
end

end