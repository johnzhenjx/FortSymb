program select_case_integer
    implicit none
    integer :: selector
    integer :: result

    read *, selector

    select case (selector)
    case (:-1)
        result = -1
        !@assert result == -1
    case (0)
        result = 0
        !@assert result == 0
    case (1, 3:5)
        result = 1
        !@assert result == 1
    case (6:)
        result = 2
        !@assert result == 2
    case default
        result = 9
        !@assert result == 9
    end select
end program select_case_integer
