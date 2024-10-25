from util import *


@apply
def apply(self):
    x, S[x] = self.of(Expr * Conjugate[Expr])
    assert x.is_super_complex
    return Equal(self, Abs(x) ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(complex=True)
    Eq << apply(x * ~x)

    Eq << algebra.expr.to.add.complex.apply(x)

    Eq << algebra.expr.to.add.complex.apply(~x)

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add, deep=True)

    Eq << algebra.eq.then.eq.abs.apply(Eq[1])

    Eq << Eq[-1] * Eq[-1]

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-3], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-25
# updated on 2023-06-28
