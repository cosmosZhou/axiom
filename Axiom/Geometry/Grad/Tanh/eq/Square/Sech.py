from util import *


@apply
def apply(self):
    x, (x, S[1]) = self.of(Derivative[tanh])
    return Equal(self, sech(x) ** 2)


@prove
def prove(Eq):
    from Axiom import Geometry, Calculus, Algebra

    x = Symbol(real=True)
    Eq << apply(Derivative[x](tanh(x)))

    Eq << Eq[0].this.find(tanh).apply(Geometry.Tanh.eq.Div)

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.Div.eq.Div.Sub)

    Eq << Eq[-1].this.find(Derivative).apply(Geometry.Grad.Sinh.eq.Cosh)

    Eq << Eq[-1].this.find(Derivative).apply(Geometry.Grad.Cosh.eq.Sinh)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(sinh).apply(Geometry.Sinh.eq.Mul.Tanh)

    Eq << Eq[-1].this.rhs.apply(Geometry.Square.Sech.eq.Sub.Square.Tanh)


if __name__ == '__main__':
    run()
# created on 2023-11-26
