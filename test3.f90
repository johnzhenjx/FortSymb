program test3
    integer :: i
    real :: vec(-1:3) = 5
    integer :: a(3) = [1, 2, 3]
    read *, i
    vec(2) = i
    !@assert vec(2) > vec(1)
end program test3