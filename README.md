# Muffins.jl
**Muffins.jl** is a Julia package for solving the **Muffin Problem**:
> *Given* __m__ *muffins and* __s__ *students, divide the muffins in such a way that all students can receive equal amounts of muffin.  
> Determine* __muffins(m, s)__*, the largest possible minimum muffin piece cut*

The Muffin Problem was first proposed by Alan Frank in 2011. Algorithms and solution methods were later extensively developed in *The Muffin Book* (2019), a collaboration between William Gasarch, Erik Metz, Jacob Prinz, and Daniel Smolyak among others.

The theorems and conjectures referenced by **Muffins.jl** are expanded upon and proven on the **[Muffin Website](https://www.cs.umd.edu/users/gasarch/MUFFINS/muffins.html)** and in *The Muffin Book*.

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

## Usage
Let `m` and `s` be positive `Int64`-type variables. Let `α` be a positive `Rational{Int64}`-type variable.

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

<!--- More method documentation to come -->

### FindProc
Run `Muffins.findproc(m, s, α)`* to display potential procedures/solutions for dividing `m` muffins among `s` students where `α` is the smallest muffin piece cut. A solutions array is returned.

### Matrix Solve
Run `Muffins.solve(m, s)` to apply linear algebra to find `muffins(m, s)`. The solution is returned. This is a work in progress in terms of speed and accuracy.

### Output mode
A an asterisk (*) is placed next to methods which have an optional `output` argument, which can be set to an integer that determines how much text the method displays:

+ Set `output` to `0` for no printing or result display
+ Set `output` to `1` for result display without proofs
+ Set `output` to `2` for detailed proofs and result display  

For example, `Muffins.half(m, s, output=1)` will display the results of the Half Method without a proof.  
By default, `output` is set to `1` for `Muffins.muffins(m, s)` and `2` for other asterisk methods.