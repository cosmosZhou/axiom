from util import *


@apply
def apply(self):
    from Axiom.Geometry.Sinh.eq.Neg.Sinh import rewrite
    return Equal(self, rewrite(sin, self), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Geometry

    x, y = Symbol(complex=True)
    Eq << apply(sin(x - y))

    Eq << Eq[0].this.lhs.apply(Geometry.Sin.eq.Sub)

    Eq << Eq[-1].this.rhs.find(Sin).apply(Geometry.Sin.eq.Sub)




if __name__ == '__main__':
    run()
# created on 2023-06-02
# updated on 2023-11-26
