program test_subroutine_calls
    implicit none

    integer :: x
    integer :: result
    integer :: values(3)

    read *, x

    values(1) = 10
    values(2) = 20
    values(3) = 30

    call update_values(x, values, result)

    !@assert result == 1
    !@assert values(1) == 11

contains
    subroutine update_values(n, arr, status)
        implicit none

        integer :: n
        integer :: arr(3)
        integer :: status

        if (n > 0) then
            arr(1) = arr(1) + 1
            status = 1

        else if (n == 0) then
            arr(2) = arr(2) + 2
            status = 0

        else
            arr(3) = arr(3) + 3
            status = -1
        end if

    end subroutine update_values

end program test_subroutine_calls