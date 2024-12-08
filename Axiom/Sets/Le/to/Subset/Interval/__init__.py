from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)
    return Subset(Interval(b, a), Interval(a, b))


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << Sets.Le.to.Eq.Interval.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1])

    Eq << Sets.IntersectFiniteSetS.subset.Interval.apply(x, y)


if __name__ == '__main__':
    run()
# created on 2020-06-03
del oo
from . import oo
from . import upper
from . import minus_oo
from . import lower
