from util import *


@apply
def apply(given, m):
    lhs, rhs = given.of(GreaterEqual)
    return GreaterEqual(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y, z = Symbol(real=True, given=True)

    Eq << apply(x >= y, z)

    Eq << Eq[-1] - y

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Min)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Min)

    Eq << Eq[0] - y

    Eq << Algebra.Ge_0.to.Eq_0.Min.apply(Eq[-1])

    Eq << Algebra.Eq.to.Eq.Min.apply(Eq[-1], -y + z)

    Eq << GreaterEqual(Min(x - y, -y + z), Min(x - y, 0, -y + z), plausible=True)

    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-05-28
