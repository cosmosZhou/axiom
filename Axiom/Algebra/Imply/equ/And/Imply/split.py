from util import *


@apply
def apply(given, *, cond=None):
    p, q = given.of(Imply)
    return And(Imply(p & cond, q), Imply(p & cond.invert(), q))


@prove
def prove(Eq):
    from Axiom import Algebra

    f, g = Function(integer=True)
    x, y = Symbol(integer=True)
    Eq << apply(Imply(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Imply.to.And.Imply.split, cond=Eq[0].find(Greater))

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.of.And.Imply.split, cond=Eq[0].find(Greater))


if __name__ == '__main__':
    run()
# created on 2023-04-25
