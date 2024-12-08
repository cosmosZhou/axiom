from util import *


@apply
def apply(self):
    x, S[x] = self.of(Expr * Conjugate[Expr])
    assert x.is_super_complex
    return Equal(self, Abs(x) ** 2)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(complex=True)
    Eq << apply(x * ~x)

    Eq << Algebra.Expr.eq.Add.complex.apply(x)

    Eq << Algebra.Expr.eq.Add.complex.apply(~x)

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Add, deep=True)

    Eq << Algebra.Eq.to.Eq.Abs.apply(Eq[1])

    Eq << Eq[-1] * Eq[-1]

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-3], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-25
# updated on 2023-06-28
