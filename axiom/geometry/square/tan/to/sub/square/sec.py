from util import *


@apply
def apply(self):
    x = self.of(tan ** 2)
    return Equal(self, sec(x) ** 2 - 1)


@prove
def prove(Eq):
    from axiom import geometry, algebra
    
    x = Symbol(real=True)
    Eq << apply(tan(x) ** 2)
    
    Eq << Eq[0].this.find(tan).apply(geometry.tan.to.div)
    
    Eq << Eq[-1].this.find(sin ** 2).apply(geometry.square.sin.to.sub.square.cos)
    
    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)
    
    Eq << Eq[-1].this.find(sec).apply(geometry.sec.to.inverse.cos)


if __name__ == '__main__':
    run()
# created on 2023-10-03
