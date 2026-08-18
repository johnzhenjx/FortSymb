program arr1
    integer :: values(5) = [10, 20, 30, 40, 50]
    integer :: i
    read *, i
    !@assert values(i) >= 10
    !@assert values(i) <= 40
end program arr1