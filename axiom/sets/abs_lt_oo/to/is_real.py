from util import *


@apply
def apply(self):
    x = self.of(Abs < Infinity)
    assert x.is_extended_real
    return Element(x, Interval(-oo, oo))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(extended_real=True)
    Eq << apply(Abs(x) < oo)

    Eq << Eq[0].this.rhs.apply(sets.el_interval.to.et)

    
    Eq << Eq[-1].this.lhs.apply(algebra.abs_lt.to.et)
    


if __name__ == '__main__':
    run()
# created on 2023-04-16
