# Muffins.jl
**Muffins.jl** is a Julia package for solving the **Muffin Problem**:
> *Given* __m__ *muffins and* __s__ *students, divide the muffins in such a way that all students can receive equal amounts of muffin.  
> Determine* __muffins(m, s)__*, the smallest piece size in the division of muffins that maximizes the smallest piece*

The Muffin Problem was first proposed by Alan Frank in 2011. Algorithms and solution methods were later extensively developed in *The Muffin Book* (2019), a collaboration between William Gasarch, Erik Metz, Jacob Prinz, and Daniel Smolyak among others.

The theorems, conjectures, and procedures referenced by **Muffins.jl** are expanded upon and proven on the **[Muffin Website](https://www.cs.umd.edu/users/gasarch/MUFFINS/muffins.html)** and in ***[The Muffin Book](https://books.google.com/books/about/Mathematical_Muffin_Morsels.html?id=UwkazAEACAAJ&source=kp_book_description)***.

For a larger, more advanced Julia package to solve more Muffin Problems, see **[The Muffin Package](https://github.com/swarman2/The-Muffin-Package)**, developed by Stephanie Warman.

## Requirements
**Muffins.jl** is built and tested for Julia v1.4.  
Download the appropriate version of Julia **[here](https://julialang.org/downloads/)**.

## Installation
Run `julia` in the terminal to open the Julia REPL and load the package by entering the following commands after the `julia>` prompt:

```julia
using Pkg
Pkg.add(PackageSpec(url="https://github.com/GeneralPoxter/Muffins.jl"))
using Muffins
```

This installs **Muffins.jl** to your local Julia environment.

## Usage
Let `m` and `s` be positive [`Int64`](https://docs.julialang.org/en/v1/manual/integers-and-floating-point-numbers/#Integers-1)-type variables. Let `α` be a positive [`Rational{Int64}`](https://docs.julialang.org/en/v1/manual/complex-and-rational-numbers/#Rational-Numbers-1)-type variable.

Including `using Muffins` to the top of any Julia file or in the Julia REPL after installation allows one to call and run any of the below methods.

### General Solution
Run `Muffins.muffins(m, s)`* to solve the Muffin Problem for `m` muffins and `s` students.  
An upper bound `α` for `muffins(m, s)` is determined by testing `(m, s)` on all of the bounding methods in the package (see **Bounding methods**). The upper bound `α` is then verified to be a lower bound for `muffins(m, s)` by finding a procedure where `α` is the smallest muffin piece cut (see **FindProc**). If all tests are conclusive, `α` is returned as the solution to `muffins(m, s)`.

### Bounding methods
#### Floor-Ceiling Theorem
Run `Muffins.fc(m, s)`* to apply the Floor-Ceiling Theorem on `(m, s)` to find an upper bound `α` for `muffins(m, s)`. `α` is returned.

#### Half Method
Run `Muffins.half(m, s)`* to apply the Half Method on `(m, s)` to find an upper bound `α` for `muffins(m, s)`. `α` is returned.  
Optionally run `Muffins.vhalf(m, s, α)`* to verify whether the Half Method can prove that the given `α` is an upper bound for `muffins(m, s)`. A boolean value is returned.

#### Interval Method
Run `Muffins.int(m, s)`* to apply the Interval Method on `(m, s)` to find an upper bound `α` for `muffins(m, s)`. `α` is returned.  
Optionally run `Muffins.vint(m, s, α)`* to verify whether the Interval Method can prove that the given `α` is an upper bound for `muffins(m, s)`. A boolean value is returned.

#### Midpoint Method
Run `Muffins.mid(m, s)`* to apply the Midpoint Method on `(m, s)` to find an upper bound `α` for `muffins(m, s)`. `α` is returned.  
Optionally run `Muffins.vmid(m, s, α)`* to verify whether the Midpoint Method can prove that the given `α` is an upper bound for `muffins(m, s)`. A boolean value is returned.

#### Easy Buddy Match
Run `Muffins.ebm(m, s)`* to apply the Easy Buddy Match on `(m, s)` to find an upper bound `α` for `muffins(m, s)`. `α` is returned.

#### Hard Buddy Match
Run `Muffins.hbm(m, s)`* to apply the Hard Buddy Match on `(m, s)` to find an upper bound `α` for `muffins(m, s)`. `α` is returned.
Optionally run `Muffins.vbhm(m, s, α)`* to verify whether the Hard Buddy Match can prove that the given `α` is an upper bound for `muffins(m, s)`. A boolean value is returned.

#### Gap Method
Run `Muffins.gap(m, s)`* to apply the Gap Method on `(m, s)` to find an upper boudn `α` for `muffins(m, s)`. `α` is returned.
Optionally run `Muffins.vgap(m, s, α)`* to verify whether the Gap Method can prove that the given `α` is an upper bound for `muffins(m, s)`. A boolean value is returned.
This version of the Gap Method does not include buddy-matching (GAPBM), which may result in inconclusive results for some `(m, s)`.

### Find Procedure
Run `Muffins.findproc(m, s, α)`* to display potential procedures/solutions for dividing `m` muffins among `s` students where `α` is the smallest muffin piece cut. A solutions array is returned. This method does not return all possible procedures.

### Matrix Solve
Run `Muffins.solve(m, s)` to apply linear algebra and **[Cbc.jl](https://github.com/jump-dev/Cbc.jl)** to find `muffins(m, s)`. The solution is returned. This is a work in progress in terms of speed and accuracy and should only be treated as a novelty.

### Output mode
An asterisk (*) is placed next to methods which have an [optional keyword argument](https://docs.julialang.org/en/v1/manual/functions/#Keyword-Arguments-1) `output`, which can be set to an integer that determines how much text the method displays:

+ Set `output` to `0` for no printing or result display
+ Set `output` to `1` for result display without proofs
+ Set `output` to `2` for detailed proofs and result display  

For example, `Muffins.half(m, s, output=1)` will display the results of the Half Method without a proof.  
By default, `output` is set to `1` for `Muffins.muffins(m, s)` and `2` for other asterisk methods.

## Accuracy
Except for **Matrix Solve** and the cases listed [here](https://docs.google.com/spreadsheets/d/1ruZvlS14-7J_UREqOEvMM_SHVeAgZnEUP0GWayFXHf0/edit?usp=sharing), all **Muffins.jl** methods are accurate for all cases not labeled with "GAPBM" listed in [test.txt](src/test.txt).  
The user is free to test **Muffins.jl** by customizing and running [test.jl](src/test.jl) (this would require accessing and modifying files in the package).

## Development
**Muffins.jl** was developed by [Antara Hebbar](https://github.com/antarahebbar) and [Jason Liu](https://github.com/GeneralPoxter) during the summer of 2020.
