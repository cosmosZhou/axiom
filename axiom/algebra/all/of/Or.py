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
    A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << ~Eq[0]

    Eq << Algebra.Any.to.Any.And.limits.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Cond.to.Eq.Bool, split=False)

    Eq << Algebra.Cond.to.Eq.Bool.invert.apply(Eq[1])

    Eq << Eq[-2].this.expr.apply(Algebra.Eq.Eq.to.Eq.trans, Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-02-17
