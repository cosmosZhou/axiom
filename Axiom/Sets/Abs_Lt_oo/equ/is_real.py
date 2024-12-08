from util import *


@apply
def apply(self):
    x = self.of(Abs < Infinity)
    assert x.is_extended_real
    return Element(x, Interval(-oo, oo))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(extended_real=True)
    Eq << apply(Abs(x) < oo)

    Eq << Eq[0].this.rhs.apply(Sets.In_Interval.equ.And)


    Eq << Eq[-1].this.lhs.apply(Algebra.LtAbs.equ.And)



if __name__ == '__main__':
    run()
# created on 2023-04-16
