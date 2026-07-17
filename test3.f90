program test3
    integer :: i
    integer :: j
    real :: vec(-1:3) = 5
    
    i = vec(2)
    !@assert i > j
end program test3