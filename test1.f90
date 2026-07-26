program test1
    implicit none

    integer :: i, x
    integer :: result = 1

    read *, x

    do i = 1, x, 2
        result = result * i
    end do
end program test1