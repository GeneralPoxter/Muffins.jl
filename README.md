# Muffins.jl
**Muffins.jl** is a Julia package for solving the **[Muffin Problem](https://www.cs.umd.edu/users/gasarch/MUFFINS/muffins.html)**:
> *Given* __m__ *muffins and* __s__ *students, divide the muffins in such a way that all students receive equal portions.  
> Determine* __α__*, the largest possible minimum muffin piece cut*

The Muffin Problem was first proposed by Alan Frank in 2011. Algorithms and solution methods were later extensively developed in *The Muffin Book* (2019), a collaboration between William Gasarch, Erik Metz, Jacob Prinz, and Daniel Smolyak among others.

The theorems and conjectures referenced by **Muffins.jl** are expanded upon and proven in *The Muffin Book*.

## Requirements
**Muffins.jl** is built and tested for Julia v1.4.  
Download the appropriate version of Julia **[here](https://julialang.org/downloads/)**.

## Installation
Run `julia` in the terminal to open the Julia REPL and load the package by entering the following commands after the `julia>` prompt:

```julia
using Pkg
Pkg.add("https://github.com/GeneralPoxter/Muffins.jl")
using Muffins
```

## Usage
Let `m` and `s` be pre-defined positive `Int64`-type variables. Let `alpha` be a pre-defined positive `Rational{Int64}`-type variable.

### General Solution
Run `Muffins.muffins(m, s)`* to solve the Muffin Problem for `m` muffins and `s` students. An upper bound for α is determined by testing (`m`, `s`) on all of the bounding methods in the package (see below). A lower bound for α is then derived by applying `Muffins.findproc(m, s, α)`.

### Bounding methods
#### Floor-Ceiling Theorem
Run `Muffins.fc(m, s)`^ to apply the Floor-Ceiling Theorem on (`m`, `s`) to find an upper bound for α.

#### Half Method
Run `Muffins.half(m, s)`* to apply the Half Method on (`m`, `s`) to find an upper bound for α.  
Optionally run `Muffins.vhalf(m, s, alpha)`* to verify whether the Half Method can prove that `alpha` is an upper bound for α.

#### Interval Method
Run `Muffins.int(m, s)`* to apply the Interval Method on (`m`, `s`) to find an upper bound for α.  
Optionally run `Muffins.vint(m, s, alpha)`* to verify whether the Interval Method can prove that `alpha` is an upper bound for α.

<!--- More method documentation to come -->

### FindProc
Run `Muffins.findproc(m, s, alpha)`^ to display potential procedures/solutions for dividing `m` muffins among `s` students where `alpha` is the smallest muffin piece cut.

### Matrix Solve
Run `Muffins.solve(m, s)` to apply linear algebra to solve the Muffin Problem. This is a work in progress in terms of speed and accuracy.

### Output mode
A symbol (* or ^) is placed next to methods which have an optional `output` argument, which can be set to an integer to determine the output mode.  

#### For methods with an asterisk (*):  
+ Set `output` to `0` for no printing or result display
+ Set `output` to `1` for result display without proofs
+ Set `output` to `2` for detailed proofs and result display  

For example, `Muffins.half(m, s, output=1)` will display the results of the Half Method without a proof.  
By default, `output` is set to `1` for `Muffins.solve(m, s)` and `2` for other asterisk methods.

#### For methods with a carat (^):
+ Set `output` to `0` for no printing and result display
+ Set `output` to `1` for result display

For example, `Muffins.findproc(m, s, alpha, output=0)` will not print anything and only return a solutions array.  
By default, `output` is set to `1` for carat methods.
