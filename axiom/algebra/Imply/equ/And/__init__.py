from util import *


@apply
def apply(self):
    p, q = self.of(boolalg.Imply)

    return And(*(p >> eq for eq in q.of(And)))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(integer=True)
    f, g, h = Function(integer=True)
    Eq << apply((x > y) >> ((f(x) > g(y)) & (h(x) > g(y))))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Imply.to.And.Imply)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.of.And.Imply)


if __name__ == '__main__':
    run()
# created on 2019-10-07
del Imply
from . import Imply
