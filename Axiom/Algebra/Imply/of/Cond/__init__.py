from util import *


@apply
def apply(given):
    p, q = given.of(Imply)
    return q


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Imply(x > y, f(x) > g(y)))

    Eq << Eq[0].this.apply(Algebra.Imply.equ.Or)

    Eq << Algebra.Or.of.Cond.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
# created on 2019-06-30
del invert
from . import invert
