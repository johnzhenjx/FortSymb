program select_case_logical
    implicit none
    logical :: selector
    integer :: result

    read *, selector

    select case (selector)
    case (.true.)
        result = 1
        !@assert result == 1
    case default
        result = 0
        !@assert result == 0
    end select
end program select_case_logical
