from util import *


@apply
def apply(given, index):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero

    eq = given.lhs.arg
    x, _x = eq.args
    assert _x == pspace(x).symbol
    n = x.shape[0]
    return Unequal(Probability(x[index]), 0)


@prove
def prove(Eq):
    from axiom import algebra, stats

    n = Symbol(domain=Range(2, oo))
    x = Symbol(real=True, shape=(n,), random=True)
    t = Symbol(domain=Range(1, n))
    Eq << apply(Unequal(Probability(x), 0), slice(0, t))

    t = Symbol(domain=Range(1, n))
    Eq << Eq[0].this.lhs.arg.apply(algebra.eq.imply.et.eq.split, t)

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-07-23
# updated on 2023-03-26
