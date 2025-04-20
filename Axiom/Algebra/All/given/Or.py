from util import *


@apply
def apply(imply):
    from Axiom.Algebra.Or.of.All import rewrite_as_Or
    return rewrite_as_Or(imply)


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(integer=True)
    f = Function(shape=(), integer=True)
    A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(All[x:A](f(x) > 0))

    Eq << ~Eq[0]

    Eq << Algebra.Any.And.of.Any.limits.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.EqBool.of.Cond, split=False)

    Eq << Algebra.EqBool.of.Cond.invert.apply(Eq[1])

    Eq << Eq[-2].this.expr.apply(Algebra.Eq.of.Eq.Eq, Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-02-17
