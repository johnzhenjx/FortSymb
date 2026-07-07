program test2
    implicit none
    integer :: n
    read *,n
    print *, fac(n)

contains
    function fac(n) result(res)
        implicit none
        integer, intent(in) :: n
        integer :: acc = 1
        integer :: res
        integer :: i
        do i=1,n
            acc = acc * i
        end do
        res = acc
    end function

end program test2