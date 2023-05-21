from util import *


@apply
def apply(lt_a, lt_b):
    x, a = lt_a.of(Less)
    S[x], b = lt_b.of(Less)
    return x < Min(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x < y, x < b)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.lt.lt.imply.lt.min)

    Eq << Eq[-1].this.lhs.apply(algebra.lt.lt.given.lt.min)

    


if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
