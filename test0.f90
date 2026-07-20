program test0
    integer, allocatable :: a(:)
    integer :: lower, upper
    read *, lower, upper
    allocate (a(lower:upper))
end program test0


