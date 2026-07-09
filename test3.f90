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
end program test3