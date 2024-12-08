from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    assert rhs > 0

    return GreaterEqual(log(lhs), log(rhs))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    y = Symbol(positive=True)
    Eq << apply(GreaterEqual(x, y))

    Eq << Eq[1].this.apply(Algebra.Ge.of.Ge_0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Log)

    Eq.is_nonnegative = Eq[0] / y - 1

    t = Symbol(nonnegative=True)
    Eq << GreaterEqual(log(1 + t), 0, plausible=True)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], t)

    t = Eq[-1].variable
    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].subs(t, Eq.is_nonnegative.lhs)
    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq.is_nonnegative, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-05-26
