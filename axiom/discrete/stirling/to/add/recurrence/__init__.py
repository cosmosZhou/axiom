from util import *


@apply
def apply(self):
    n, k = self.of(Stirling)
    n -= 1
    k -= 1
    return Equal(self, Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    k, n = Symbol(integer=True, positive=True)
    Eq << apply(Stirling(n + 1, k + 1))

    Eq << Eq[0].apply(algebra.cond.of.et.all, cond=k < n)

    Eq << algebra.et.of.et.apply(Eq[-1])

    k_ = Symbol('k', domain=Range(1, n))
    Eq << discrete.stirling.to.add.recurrence.k_less_than_n.apply(n, k_)

    Eq << Eq[-1].apply(algebra.cond.then.all.restrict, (k_,))

    Eq << algebra.all.of.et.all.apply(Eq[-2], cond=n.set)

    Eq << Eq[-1].this().expr.simplify()




if __name__ == '__main__':
    run()

# created on 2020-10-06
# updated on 2023-08-26
from . import k_less_than_n
