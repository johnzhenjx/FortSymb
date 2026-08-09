program select_case_halt
    implicit none
    integer :: selector
    integer :: result

    read *, selector

    select case (selector)
    case (0)
        !@assert .false.
        result = 1
        !@assert result == 1
    case default
        result = 2
        !@assert result == 2
    end select
end program select_case_halt
