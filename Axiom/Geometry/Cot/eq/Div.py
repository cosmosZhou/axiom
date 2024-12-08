from util import *


@apply
def apply(self):
    x = self.of(cot)
    return Equal(self, cos(x) / sin(x))


@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(cot(x))

    Eq << Eq[0].this.lhs.apply(Geometry.Cot.eq.Inv.Tan)

    Eq << Eq[-1].this.find(tan).apply(Geometry.Tan.eq.Div)




if __name__ == '__main__':
    run()
# created on 2023-10-03
# updated on 2023-11-26
