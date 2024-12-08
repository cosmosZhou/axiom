from util import *


@apply
def apply(self, *, cond=None, wrt=None, evaluate=False):
    from Axiom.Algebra.Sum.eq.Add.split import split
    return split(All, self, cond, wrt=wrt)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(All[x:A](f(x) > 0), cond=B)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(Algebra.All.All.of.All.limits_union)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.All.to.All.limits_union)


if __name__ == '__main__':
    run()

# created on 2018-04-23
