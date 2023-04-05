from util import *


@apply
def apply(all_ge):
    (fx, m), *limits = all_ge.of(All[GreaterEqual])
    return Minima(fx, *limits) >= m


@prove
def prove(Eq):
    from axiom import algebra
    
    m = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    S = Symbol(etype=dtype.real, given=True)
    Eq << apply(All[x:S](f(x) >= m))
    
    Eq << ~Eq[-1]
    
    Eq << algebra.lt_minima.imply.all_lt.apply(Eq[-1])
    
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2023-03-25
