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
- `select case` with integer values and ranges, logical values, and `case default`


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
- Multidimensional arrays, with dimensions listed in attribute or on name
- Can be initially uninitialised, constant scalar init + assign, array-constructor init + assign
- Allocatable arrays


### Array Access

- Reading a single array element
- Symbolic array indices
- Multidimensional indexing
- Bounds checking for every dimension
- Subscript-triplet sections with omitted bounds and positive or negative strides
- Rank reduction for matrix rows and columns, e.g. `matrix(i, :)` and `matrix(:, j)`


### Array Updates

- Updating a single array element
- Symbolic update indices
- Bounds checking for every dimension
- Assigning arrays or scalar values to array sections
- Shape checking for section-to-array and array-to-section assignment

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


### LOOPS

- Do with integer initial, limit and increment, loop max in flags
- IncrementStepNonZero obligation
- Do while
- No names right now


### Functions
- FUNCTIONS WORK WITH NAMED + POSITIONAL (no subprograms )
- subroutines also work
- intents work
- recursion up to user-specified max call depth


## Currently Unsupported Features

- Vector-subscript array sections, e.g. `a([1, 3, 5])`
- Implied-`do` array constructors
- Nested or array-valued constructor elements
- Element-wise array arithmetic
- Assumed-shape arrays
- General procedure calls
- Modules
- Derived types
- Character and complex types
- General intrinsic functions
- Formatted input and output
- Pointers
- Other types