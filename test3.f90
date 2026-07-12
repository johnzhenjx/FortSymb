program test3
    integer :: i = 5
    integer :: j
    logical :: b = .false.
    real :: x
    read *, j
    if(i > j) b = .true.
    if(i > j) then
        x = 1
    else if(i==j) then 
        x = 0
    else 
        x = -1
    end if
    x = i / j
    !@assert x > 0
end program test3