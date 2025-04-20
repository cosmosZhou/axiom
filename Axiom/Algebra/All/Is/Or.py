from util import *


@apply
def apply(imply):
    from Axiom.Algebra.Or.of.All import rewrite_as_Or
    return rewrite_as_Or(imply)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Or.of.All)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.given.Or)


if __name__ == '__main__':
    run()

# created on 2018-12-23
