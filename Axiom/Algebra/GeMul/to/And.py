from util import *


@apply
def apply(given):
    factor, cond = given.of(GreaterEqual[Mul[Bool], 1])
    return factor >= 1, cond


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(GreaterEqual(Bool(f(x) >= 0) * y, 1))

    Eq << Algebra.Ge.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Or.split.Mul.apply(Eq[-1])

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Cond.apply(Eq[-1])

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[-1])

    Eq << LessEqual(Eq[-1].lhs, 1, plausible=True)

    Eq << Algebra.Ge.Le.to.Eq.apply(Eq[-2], Eq[-1])

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-11-05
