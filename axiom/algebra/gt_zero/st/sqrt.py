from util import *


@apply
def apply(given):
    x = given.of(Expr ** S.Half > 0)
    assert x.is_real
    return x > 0


@prove
def prove(Eq):
    from axiom import algebra
    
    x = Symbol(real=True)
    Eq << apply(sqrt(x) > 0)
    
    Eq << Eq[0].this.rhs.apply(algebra.gt_zero.sqrt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
