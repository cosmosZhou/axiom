from util import *


@apply
def apply(self, i=None):
    n = self.of(Factorial2)
    assert n.is_odd
    k = (n + 1) / 2
    assert k >= 0
    if i is None:
        i = self.generate_var(integer=True)
    return Equal(self, Product[i: 1: k + 1](2 * i - 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Factorial2(n * 2 - 1), i)

    Eq << Eq[-1].this.lhs.apply(discrete.factorial2.to.prod, i)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.limits.subs.negate, i, n - i)

    # https://en.wikipedia.org/wiki/Double_factorial



if __name__ == '__main__':
    run()
# created on 2023-06-03
