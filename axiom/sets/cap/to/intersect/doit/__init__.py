from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.doit import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from axiom import sets
    n = 5
    x = Symbol(etype=dtype.real, shape=(n,))
    i = Symbol(integer=True)

    Eq << apply(Cap[i](x[i]))

    Eq << Eq[-1].this.lhs.apply(sets.cap.limits.domain_defined)

    n -= 1
    Eq << Eq[-1].this.lhs.apply(sets.cap.to.intersect.split, {n})

    n -= 1
    Eq << Eq[-1].find(Cap).this.apply(sets.cap.to.intersect.split, {n})

    n -= 1
    Eq << Eq[-1].rhs.find(Cap).this.apply(sets.cap.to.intersect.split, {n})

    n -= 1
    Eq << Eq[-1].rhs.find(Cap).this.apply(sets.cap.to.intersect.split, {n})

    Eq << Eq[4].subs(Eq[-1])

    Eq << Eq[3].subs(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])


if __name__ == '__main__':
    run()

from . import outer
from . import setlimit
# created on 2021-01-20
