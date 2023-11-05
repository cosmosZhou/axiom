from util import *


@apply
def apply(x):
    return Equal(cot(x) * tan(x), 1)


@prove
def prove(Eq):
    from axiom import geometry
    
    x = Symbol(real=True)
    Eq << apply(x)
    
    Eq << Eq[0].this.find(cot).apply(geometry.cot.to.inverse.tan)


if __name__ == '__main__':
    run()
# created on 2023-10-03
