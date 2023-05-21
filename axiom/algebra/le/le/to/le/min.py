from util import *


@apply
def apply(le_a, le_b):    
    x, a = le_a.of(LessEqual)
    S[x], b = le_b.of(LessEqual)
    return x <= Min(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x <= y, x <= b)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.le.le.imply.le.min)

    Eq << Eq[-1].this.lhs.apply(algebra.le.le.given.le.min)

    


if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
