from util import *


@apply
def apply(self):
    x = self.of(cos)
    return Equal(self, cos(-x), evaluate=False)


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(complex=True)
    Eq << apply(cos(x - y))

    
    Eq << Eq[0].this.lhs.apply(geometry.cos.to.add.principle.sub)
    Eq << Eq[-1].this.rhs.apply(geometry.cos.to.add.principle.sub)
    


if __name__ == '__main__':
    run()
# created on 2023-05-20
