program recurse
    implicit none
    integer :: result

    result = fib(10)
    !@assert result == 55

contains
    recursive integer function fib(n) result(r)
        integer :: n

        if (n <= 1) then
            r = n
        else
            r = fib(n-1) + fib(n-2)
        endif
    end function
end program recurse
