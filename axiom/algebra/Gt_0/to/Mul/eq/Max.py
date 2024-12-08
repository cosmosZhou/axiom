from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    args = self.of(Max)
    return Equal(self * a, Max(*(arg * a for arg in args)))


@prove
def prove(Eq):
    from Axiom import Algebra

    a, x, y, z = Symbol(real=True, given=True)
    Eq << apply(a > 0, Max(x, y, z))

    b = Symbol(positive=True)
    Eq << Max(x * b, y * b, z * b).this.apply(Algebra.Max.eq.Mul)

    Eq << Eq[-1].subs(b, a)

    Eq << Eq[-1].this.args[1].simplify()

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-08-18
