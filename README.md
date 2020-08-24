# Muffins.jl
**Muffins.jl** is a Julia package for solving the **Muffin Problem**:
> *Given* __m__ *muffins and* __s__ *students, divide the muffins in such a way that all students can receive equal amounts of muffin.  
> Determine* __muffins(m, s)__*, the smallest piece size in the distribution of muffins that maximizes the smallest piece*

The Muffin Problem was first proposed by Alan Frank in 2011. Algorithms and solution methods were later extensively developed in *The Muffin Book* (2019), a collaboration between William Gasarch, Erik Metz, Jacob Prinz, and Daniel Smolyak, among others.

The theorems, conjectures, and procedures referenced by **Muffins.jl** are expanded upon and proven on the [Muffin Website](https://www.cs.umd.edu/users/gasarch/MUFFINS/muffins.html) and in *[The Muffin Book](https://books.google.com/books/about/Mathematical_Muffin_Morsels.html?id=UwkazAEACAAJ&source=kp_book_description)*.

For a larger, more advanced Julia package to solve more Muffin Problems, see [The Muffin Package](https://github.com/swarman2/The-Muffin-Package), developed by Stephanie Warman.

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

Include `using Muffins` at the top of any Julia file or in the Julia REPL after installation to run any of the below methods.

## Usage
Let `m` and `s` be positive [`Int64`](https://docs.julialang.org/en/v1/manual/integers-and-floating-point-numbers/#Integers-1)-type variables. Let `α` be a positive [`Rational{Int64}`](https://docs.julialang.org/en/v1/manual/complex-and-rational-numbers/#Rational-Numbers-1)-type variable.

### General Solution
To solve the Muffin Problem for `m` muffins and `s` students:
```julia
Muffins.muffins(m, s)
```  
An upper bound `α` for `muffins(m, s)` is found by testing `(m, s)` on all the bounding methods in the package (see **Bounding methods**). The upper bound `α` is then verified to be a lower bound for `muffins(m, s)` by finding a procedure where `α` is the smallest muffin piece cut (see **Find Procedure**). If all tests are conclusive, `α` is returned as the solution to `muffins(m, s)`. Else, the method returns `1//1`.

### Bounding methods
Given `(m, s)`, each bounding method finds and returns the upper bound `α` for `muffins(m, s)`.

Most bounding methods also have a v-method that returns a boolean, verifying whether that bounding method can prove that the given `α` is an upper bound for `muffins(m, s)`.

+ #### Floor-Ceiling Theorem
    To find upper bound `α`:
    ```julia
    Muffins.fc(m, s)
    ```
    No v-method

+ #### Half Method
    To find upper bound `α`:
    ```julia
    Muffins.half(m, s)
    ```
    To verify `α`:
    ```julia
    Muffins.vhalf(m, s, α)
    ```

+ #### Interval Method
    To find upper bound `α`:
    ```julia
    Muffins.int(m, s)
    ```
    To verify `α`:
    ```julia
    Muffins.vint(m, s, α)
    ```

+ #### Midpoint Method
    To find upper bound `α`:
    ```julia
    Muffins.mid(m, s)
    ```
    To verify `α`:
    ```julia
    Muffins.vmid(m, s, α)
    ```

+ #### Easy Buddy Match
    To find upper bound `α`:
    ```julia
    Muffins.ebm(m, s)
    ```
    No v-method

+ #### Hard Buddy Match
    To find upper bound `α`:
    ```julia
    Muffins.hbm(m, s)
    ```
    No v-method

+ #### Gap Method
    To find upper bound `α`:
    ```julia
    Muffins.gap(m, s)
    ```
    To verify `α`:
    ```julia
    Muffins.vgap(m, s, α)
    ```

### Find Procedure
To find potential procedures/solutions for dividing `m` muffins among `s` students where `α` is the smallest muffin piece cut:
```julia
Muffins.findproc(m, s, α)
```
Returns an array of solutions. This method does not return all possible procedures.

### Matrix Solve
To apply linear algebra and [Cbc.jl](https://github.com/jump-dev/Cbc.jl) to find `muffins(m, s)`:
```julia
Muffins.solve(m, s)
```
Returns the solution `α`. This is a work in progress in terms of speed and accuracy and should only be treated as a novelty.

### Output mode
All methods except for **Matrix Solve** can display their results and justify the process with a proof. How much text is displayed is determined by the [optional keyword argument](https://docs.julialang.org/en/v1/manual/functions/#Keyword-Arguments-1) `output`:

+ Set `output` to `0` for no printing or result display
+ Set `output` to `1` for result display without proofs
+ Set `output` to `2` for detailed proofs and result display  

For example, `Muffins.half(m, s, output=1)` will display the results of the Half Method without a proof.  
By default, `output` is set to `1` for `Muffins.muffins(m, s)` and `2` for other asterisk methods.

## Accuracy
Except for **Matrix Solve** and the cases listed [here](https://docs.google.com/spreadsheets/d/1ruZvlS14-7J_UREqOEvMM_SHVeAgZnEUP0GWayFXHf0/edit?usp=sharing), all **Muffins.jl** methods are correct for all cases listed in [test.txt](src/test.txt).  
The user is free to test **Muffins.jl** by customizing and running [test.jl](src/test.jl) (this would require accessing and modifying files in the package).

## Development
**Muffins.jl** was developed by [Antara Hebbar](https://github.com/antarahebbar) and [Jason Liu](https://github.com/GeneralPoxter) during the summer of 2020.
