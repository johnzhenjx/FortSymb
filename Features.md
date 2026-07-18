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

## Assertions

- User assertions written as comments using:

```fortran
!@assert condition
```

- Assertions over symbolic program values
- Assertion checking under the path conditions of each execution state
- Counterexample generation for failing assertions

## Proof Obligations

- Division-by-zero checks
- Array-bounds checks
- User assertion checks

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

### Array Declarations

- One-dimensional arrays
- Multidimensional arrays
- Explicit lower and upper bounds
- Default lower bound of `1`
- Constant scalar initialisation of every array element (only currently supported method of initialisation)

Examples:

```fortran
real :: vec(5)
real :: vec(-1:3)
integer :: matrix(2, 3) = 0
logical :: flags(10) = .false.
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
- Multidimensional single element updates
- Assignment conversion based on the array element type
- Bounds checking on updates

Examples:

```fortran
vec(i) = 10
matrix(i, j) = value
```

## Currently Unsupported Features

- Array sections and slices
- Whole-array assignment
- Assigning a matrix row or column to a vector
- `IxRange` expressions such as `a(:)` or `a(1:5)`
- Array constructors such as `[1, 2, 3]`
- Element-wise array arithmetic
- Dynamic allocation
- Allocatable arrays
- Assumed-shape arrays
- Functions and subroutines
- Procedure calls
- Modules
- Derived types
- Character and complex types
- Loops
- `select case`
- General intrinsic functions
- Formatted input and output