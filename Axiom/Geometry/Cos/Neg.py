from util import *


@apply
def apply(self):
    from Axiom.Algebra.Abs.Neg import rewrite
    return Equal(self, rewrite(cos, self), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Geometry

    x, y = Symbol(complex=True)
    Eq << apply(cos(x - y))

    Eq << Eq[0].this.lhs.apply(Geometry.Cos.eq.Sub)

    Eq << Eq[-1].this.rhs.apply(Geometry.Cos.eq.Sub)





if __name__ == '__main__':
    run()
# created on 2023-05-20
# updated on 2023-11-26
