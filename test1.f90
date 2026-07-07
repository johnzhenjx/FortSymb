program test1
    implicit none
    real :: r
    read *, r
    print *, sphere_surface_area(r)

contains
    function sphere_surface_area(r) result(A)
        implicit none
        real, intent(in) :: r
        real, parameter  :: pi = 3.1416
        real             :: A
        A = 4 * pi * r**2
    end function
end program test1

