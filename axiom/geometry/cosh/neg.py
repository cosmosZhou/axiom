from util import *


@apply
def apply(self):
    from axiom.algebra.abs.neg import rewrite
    return Equal(self, rewrite(cosh, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(complex=True)
    Eq << apply(cosh(x - y))

    Eq << Eq[0].this.lhs.apply(geometry.cosh.to.add)

    Eq << Eq[-1].this.rhs.apply(geometry.cosh.to.add)

    


if __name__ == '__main__':
    run()
# created on 2023-11-26
