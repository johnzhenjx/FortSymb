program test3
    integer :: i
    real :: vec(-1:3) = 5
    read *, i
    vec(2) = i
    !@assert vec(2) > vec(1)
end program test3