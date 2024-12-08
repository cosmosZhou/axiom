from util import *


@apply
def apply(given, *, cond=None, wrt=None):
    from Axiom.Algebra.All.to.And.All.split import split
    given = split(All, given, cond, wrt)
    return given


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    f = Function(integer=True, shape=())
    d = Symbol(real=True, positive=True)
    Eq << apply(All[x:Interval(-d, d, left_open=True, right_open=True)](f(x) > 0), cond=x < 0)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.All.to.And.All.split, cond=x < 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.of.And.All.split, cond=x < 0)


if __name__ == '__main__':
    run()
# created on 2023-10-22
