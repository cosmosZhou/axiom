from util import *


@apply
def apply(self):
    x, (x, S[1]) = self.of(Derivative[tan])
    return Equal(self, sec(x) ** 2)


@prove
def prove(Eq):
    from Axiom import Geometry, Calculus

    x = Symbol(real=True)
    Eq << apply(Derivative[x](tan(x)))

    Eq << Eq[0].this.find(tan).apply(Geometry.Tan.eq.Div)

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.Div.eq.Div.Sub)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(cos ** 2).apply(Geometry.Square.Cos.eq.Sub.Square.Sin)

    Eq << Eq[-1].this.find(cos).apply(Geometry.Cos.eq.Inv.Sec)



if __name__ == '__main__':
    run()
# created on 2023-11-26
