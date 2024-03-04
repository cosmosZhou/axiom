from util import *


@apply
def apply(self):
    x = self.of(sinh)
    return Equal(self, 1 / csch(x))


@prove
def prove(Eq):
    from axiom import geometry
    
    x = Symbol(real=True)
    Eq << apply(sinh(x))
    
    Eq << Eq[0].this.find(csch).apply(geometry.csch.to.inverse.sinh)


if __name__ == '__main__':
    run()
# created on 2023-11-26
