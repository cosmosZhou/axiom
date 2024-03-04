from util import *


@apply
def apply(self):
    x = self.of(sin)
    return Equal(self, 1 / csc(x))


@prove
def prove(Eq):
    from axiom import geometry
    
    x = Symbol(real=True)
    Eq << apply(sin(x))
    
    Eq << Eq[0].this.find(csc).apply(geometry.csc.to.inverse.sin)


if __name__ == '__main__':
    run()
# created on 2023-11-26
