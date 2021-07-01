from util import *


@apply
def apply(fraction):
    x = fraction.of(FractionalPart)
     
    return Equal(fraction, x - floor(x))


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(frac(x))    

    
if __name__ == '__main__':
    run()