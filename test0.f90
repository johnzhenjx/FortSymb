program test0
    integer, allocatable :: a(:)
    integer :: lower, upper
    read *, lower, upper
    allocate (a(lower:upper))
    a(0) = 1
end program test0


