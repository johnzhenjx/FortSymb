program rectangle2
    integer :: w, l, area
    read *, w,l
    area = calculate_rectangle_area(w, l)

    !@assert area >= 0

contains
    integer function calculate_rectangle_area(width, length)
        integer :: width, length
        calculate_rectangle_area = width * length
    end function calculate_rectangle_area
end program rectangle2