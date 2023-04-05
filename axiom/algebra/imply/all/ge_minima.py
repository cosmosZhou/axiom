from util import *


@apply
def apply(self):
    function, *limits = self.of(Minima)
    return All(GreaterEqual(function, self), *limits)


@prove
def prove(Eq):
    from axiom import algebra
    
    x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Minima[x:S](f(x)))
    
    Eq << algebra.imply.all.minima_le.apply(Eq[0].find(Minima))
    
    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2023-03-28
