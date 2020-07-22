# Muffins Package
The **Muffins Package** is a Julia package for solving the **[Muffin Problem](https://www.cs.umd.edu/users/gasarch/MUFFINS/muffins.html)**:
> *Given* **m** *muffins and* **s** *students, divide the muffins in such a way that all students receive equal portions.  
> Determine* **α** *, the largest possible minimum muffin piece cut*

The Muffin Problem was first proposed by Alan Frank in 2011. Algorithms and solution methods were later extensively developed in *The Muffin Book* (2019), a collaboration between William Gasarch, Erik Metz, Jacob Prinz, and Daniel Smolyak among others.

The theorems and conjectures referenced by the **Muffins Package** are expanded upon and proven in *The Muffin Book*.

## Requisites
The **Muffins Package** is built and tested for Julia v1.4.  
Download the appropriate version of Julia **[here](https://julialang.org/downloads/)**

## Installation
<!--- Installation instructions subject to change - will soon incorporate Pkg.add() -->
Download the repository from Github and navigate to the package directory.  
Run `julia` in the terminal to open the Julia REPL and load the package:

```julia
julia> using Pkg
julia> Pkg.activate(".")
julia> import Muffins
```

## Usage
Let `m` and `s` be pre-defined positive `Int64`-type variables. Let `alpha` be a pre-defined positive `Rational{Int64}`-type variable. All commands should be run in the Julia REPL after loading the package.

### General Solution
Run `Muffins.muffins(m, s)` to solve the Muffin Problem for `m` muffins and `s` students. An upper bound for α is determined by testing (`m`, `s`) on all of the bounding methods in the package (see below). A lower bound for α is then derived by applying `Muffins.findproc(m, s, α)`.  
Optionally run `Muffins.muffins(m, s, proof=false)` to prevent proof output in the solution. By default, `proof` is set to `true`.

### Bounding Methods
Asterisks (*) are placed next to methods which have an optional `proof` field, which can be set to `true` for proof output or `false` for simplified result display. `proof` is always set to `true` by default. (The `Muffins.muffins(m, s)` method above has a similar optional `proof` field)

#### Floor-Ceiling Theorem
Run `Muffins.fc(m, s)` to apply the Floor-Ceiling Theorem on (`m`, `s`) to find an upper bound for α.

#### Half Method
Run `Muffins.half(m, s)`* to apply the Half Method on (`m`, `s`) to find an upper bound for α.  
Optionally run `Muffins.vhalf(m, s, alpha)`* to verify whether the Half Method can be applied to prove that `alpha` is an upper bound for α.

#### Interval Method
Run `Muffins.int(m, s)`* to apply the Interval Method on (`m`, `s`) to find an upper bound for α.
Optionally run `Muffins.vint(m, s, alpha)`* to verify whether the Interval Method can be applied to prove that `alpha` is an upper bound for α.

<!--- More method documentation to come -->

### FindProc
Run `Muffins.findproc(m, s, alpha)` to display potential procedures for dividing `m` muffins among `s` students where `alpha` is the smallest muffin piece cut.

### Matrix Solve
Run `Muffins.solve(m, s)` to apply linear algebra and matrices to solve the Muffin Problem.