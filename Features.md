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
- Multidimensional arrays, with dimensions listed in attribute or on name
- Can be initially uninitialised, constant scalar init + assign, array-constructor init + assign
- Allocatable arrays


### Array Access

- Reading a single array element
- Symbolic array indices
- Multidimensional indexing
- Bounds checking for every dimension


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


### LOOPS

- Do while with integer initial, limit and increment, loop max in flags
- No names right now


### Functions
- FUNCTIONS WORK WITH NAMED + POSITIONAL (no subprograms or recursion for now)
- subroutines also work (disregarding intents for now)


## Currently Unsupported Features

- Array sections and slices
- Assigning a matrix row or column to a vector
- `IxRange` expressions for assign, e.g. `a(1:5)`
- Implied-`do` array constructors
- Nested or array-valued constructor elements
- Element-wise array arithmetic
- Assumed-shape arrays
- General procedure calls
- Modules
- Derived types
- Character and complex types
- Loops
- `select case`
- General intrinsic functions
- Formatted input and output