from util import *


@apply
def apply(x):
    return Equal(sec(x) * cos(x), 1)


@prove
def prove(Eq):
    from axiom import geometry
    
    x = Symbol(real=True)
    Eq << apply(x)
    
    Eq << Eq[0].this.find(sec).apply(geometry.sec.to.inverse.cos)


if __name__ == '__main__':
    run()
# created on 2023-10-03
