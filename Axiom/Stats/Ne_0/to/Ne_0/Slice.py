from util import *


@apply
def apply(ne_zero, index):
    lhs, rhs = ne_zero.of(Unequal[Probability[Equal], 0])

    return Unequal(Probability(Equal(lhs[index], rhs[index])), 0)


@prove
def prove(Eq):
    from Axiom import Algebra, Stats

    n = Symbol(domain=Range(2, oo))
    x = Symbol(real=True, shape=(n,), random=True)
    t = Symbol(domain=Range(1, n))
    Eq << apply(Unequal(Probability(x), 0), slice(0, t))

    t = Symbol(domain=Range(1, n))
    Eq << Eq[0].this.lhs.arg.apply(Algebra.Eq.to.And.Eq.split, t)

    Eq << Stats.Ne_0.to.And.Ne_0.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-07-23
# updated on 2023-03-26