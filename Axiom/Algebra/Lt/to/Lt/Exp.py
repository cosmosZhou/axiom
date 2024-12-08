from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Less)

    return Less(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Less(x, y))

    t = Symbol(y - x)
    Eq << t.this.definition

    Eq << Algebra.Lt.to.Gt_0.apply(Eq[0])

    Eq.gt_zero = Algebra.Eq.Gt.to.Gt.subs.apply(Eq[-2], Eq[-1])

    Eq << Eq[-2] + x

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1] / exp(x)

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Exp)

    r = Symbol(positive=True)
    Eq << Greater(exp(r), 1, plausible=True)

    Eq << Algebra.Cond.to.All.apply(Eq[-1])

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].find(Symbol), t)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq.gt_zero, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-16
