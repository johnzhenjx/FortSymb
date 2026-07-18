program test3
    integer :: i
    integer :: j
    integer :: a(-1:2) = [1, 2, 3, 4]
    read *, i
    read*, j
    a(i) = j
    !@assert a(i) > a(-1)
end program test3