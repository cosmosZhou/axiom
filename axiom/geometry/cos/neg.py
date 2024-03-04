from util import *


@apply
def apply(self):
    from axiom.algebra.abs.neg import rewrite
    return Equal(self, rewrite(cos, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(complex=True)
    Eq << apply(cos(x - y))

    Eq << Eq[0].this.lhs.apply(geometry.cos.to.sub)

    Eq << Eq[-1].this.rhs.apply(geometry.cos.to.sub)

    
    


if __name__ == '__main__':
    run()
# created on 2023-05-20
# updated on 2023-11-26
