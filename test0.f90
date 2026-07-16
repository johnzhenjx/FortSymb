program test0
    integer :: x = 2
    real :: test(x)
    real:: r, pi, vl, sarea
    pi=3.1416
    read *,r 
    if(r<=0) then
        print *,"Bad radius"
    else
        vl=(4./3)*pi*r**3
        sarea=4*pi*r**2 
        print *,"Volume is ",vl,"surface area is",sarea
    end if
end program test0


