from util import *


@apply
def apply(self):
    x, S[x] = self.of(Expr - Conjugate[Expr])    
    assert x.is_complex
    return Equal(self, 2 * Im(x) * S.ImaginaryUnit)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(complex=True)
    Eq << apply(x - ~x)

    Eq << algebra.expr.to.add.complex.apply(x)

    Eq << algebra.expr.to.add.complex.apply(~x)

    Eq << Eq[-2] - Eq[-1]

    


if __name__ == '__main__':
    run()
# created on 2023-05-25
