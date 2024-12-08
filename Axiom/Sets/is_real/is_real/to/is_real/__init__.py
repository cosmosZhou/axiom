from util import *


def interval_is_real(interval):
    if interval.is_Interval:
        if interval.start.is_finite or interval.left_open:
            if interval.stop.is_finite or interval.right_open:
                return True
@apply
def apply(a_is_real, b_is_real):
    a, aR = a_is_real.of(Element)
    b, bR = b_is_real.of(Element)
    assert interval_is_real(aR)
    assert interval_is_real(bR)
    return Element(a * b, Reals)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Reals), Element(y, Reals))

    Eq << Sets.In.to.Any.Eq.apply(Eq[0], var='a')

    Eq << Sets.In.to.Any.Eq.apply(Eq[1], var='b')

    Eq << Algebra.Any.Any.to.Any.And.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.to.Eq.Mul)

    a, b = Eq[-1].variables
    c = Symbol(real=True)
    Eq << Algebra.Any.to.Any.subs.apply(Eq[-1], a * b, c)




if __name__ == '__main__':
    run()
# created on 2022-04-03
# updated on 2023-05-03
del Add
from . import Add
from . import Sub
