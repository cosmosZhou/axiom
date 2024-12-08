from util import *


@apply
def apply(imply):
    from Axiom.Algebra.All.to.Or import rewrite_as_Or
    return rewrite_as_Or(imply)


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.to.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.Or)


if __name__ == '__main__':
    run()

# created on 2018-12-23
