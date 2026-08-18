program arr2
    integer :: values(4) = [10, 20, 30, 40]
    integer :: choice

    read *, choice

    if (choice > 0) then
        values(2:4) = 100
    else
        values(2:4) = 0
    endif

    !@assert values(1) == 10
    !@assert values(4) == 100
end program arr2