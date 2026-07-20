# FortSymb Supported Features

## Program Structure

- Fortran 90 main programs
- Variable declarations
- Scalar assignments
- Array-element assignments
- Conditional statements
- Simple input statements
- Assertion comments

## Supported Data Types

- `integer`
- `real`
- `logical`

## Scalar Variables

- Declaration with or without an initial value
- Reading and updating scalar variables
- Detection of use before initialisation
- Type-aware assignment
- Integer-to-real conversion
- Real-to-integer conversion
- Logical assignment

## Expressions

### Arithmetic

- Addition
- Subtraction
- Multiplication
- Division
- Unary plus
- Unary minus
- Mixed integer and real arithmetic

### Comparisons

- Equal to
- Not equal to
- Less than
- Less than or equal to
- Greater than
- Greater than or equal to

### Logical Operations

- `.and.`
- `.or.`
- `.xor.`
- `.not.`

## Input

- List-directed scalar input using `read *`
- Symbolic integer, real, and logical input values

## Control Flow

- Single-line `if` statements
- Block `if` statements
- `else if`
- `else`
- Nested conditionals
- Symbolic branching into multiple execution states


## Proof Obligations

- Division-by-zero checks
- Array-bounds checks (indexing outside bounds)
- Array-shape checks (on assignment to arrays)
- User assertion checks 
```fortran
!@assert condition
```

## Solver Support

- Satisfiability checking with Z3
- Detection of feasible and infeasible execution paths
- Removal of infeasible symbolic states
- Counterexample extraction from satisfiable error conditions

## Arrays

### Supported Array Types

- Integer arrays
- Real arrays
- Logical arrays

### Array Declarations + Initialisations
- Multidimensional arrays, initially uninitialised, constant scalar init + assign, array-constructor init + assign

Examples:

```fortran
real :: vec(5)
real :: vec(-1:3)
integer :: matrix(2, 3) = 0
logical :: flags(10) = .false.

integer :: values(3) = [1, 2, 3]
real :: coefficients(3) = [1, 2.5, 3]
integer :: matrix2(2, 2) = [1, 2, 3, 4]
```

Array-constructor elements are assigned in Fortran array-element order, with the first dimension varying fastest.

For example:

```fortran
integer :: matrix(2, 2) = [1, 2, 3, 4]
```

corresponds to:

```fortran
matrix(1, 1) = 1
matrix(2, 1) = 2
matrix(1, 2) = 3
matrix(2, 2) = 4
```

### Array Access

- Reading a single array element
- Symbolic array indices
- Multidimensional indexing
- Bounds checking for every dimension

Examples:

```fortran
x = vec(i)
x = matrix(i, j)
```

### Array Updates

- Updating a single array element
- Symbolic update indices
- Bounds checking for every dimension

Examples:

```fortran
vec(i) = 10
matrix(i, j) = value
```

### Array Constructor Limitations

The following constructor features are not currently supported:

- Implied-`do` constructors
- Nested array constructors
- Array copy constructors
- Shape obligations on vector-constructor and assignment
- Reshape init + assign
- Constructor type specifications
- Character array constructors
- Complex array constructors

## Currently Unsupported Features

- Array sections and slices
- Whole-array assignment
- Assigning a matrix row or column to a vector
- `IxRange` expressions such as `a(:)` or `a(1:5)`
- Implied-`do` array constructors
- Nested or array-valued constructor elements
- Element-wise array arithmetic
- Scalar broadcasting in array expressions
- Dynamic allocation
- Allocatable arrays
- Assumed-shape arrays
- Functions and subroutines
- General procedure calls
- Modules
- Derived types
- Character and complex types
- Loops
- `select case`
- General intrinsic functions
- Formatted input and output