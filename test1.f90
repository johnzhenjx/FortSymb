program test1
    implicit none

    integer :: x
    integer :: result
    integer :: values(3)

    read *, x

    values(1) = 10
    values(2) = 20
    values(3) = 30

    result = choose_element(values, x)

    !@assert result == 10 .or. result == 20

contains

    integer function choose_element(array, selector)
        implicit none

        integer :: array(3)
        integer :: selector

        if (selector < 0) then
            choose_element = array(1)
        else if (selector == 0) then
            choose_element = array(2)
        else
            choose_element = array(3)
        end if
    end function choose_element

end program test1