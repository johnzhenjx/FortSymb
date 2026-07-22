program test1
    implicit none
    real :: w,h
    real :: A
    read *, w,h
    A = rectangle_area(w,h)
    !@assert A > 0
contains
    function rectangle_area(w,h) result(A)
        implicit none
        real, intent(in) :: w,h
        real             :: A
        A = w * h
    end function
end program test1

