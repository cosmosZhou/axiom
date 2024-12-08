from util import *


@apply
def apply(self):
    n, k = self.of(Stirling)
    n -= 1
    k -= 1
    return Equal(self, Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    k, n = Symbol(integer=True, positive=True)
    Eq << apply(Stirling(n + 1, k + 1))

    Eq << Eq[0].apply(Algebra.Cond.of.And.All, cond=k < n)

    Eq << Algebra.And.of.And.apply(Eq[-1])

    k_ = Symbol('k', domain=Range(1, n))
    Eq << Discrete.Stirling.eq.Add.recurrence.k_Less_than_n.apply(n, k_)

    Eq << Eq[-1].apply(Algebra.Cond.to.All.restrict, (k_,))

    Eq << Algebra.All.of.And.All.apply(Eq[-2], cond=n.set)

    Eq << Eq[-1].this().expr.simplify()




if __name__ == '__main__':
    run()

# created on 2020-10-06
# updated on 2023-08-26
from . import k_Less_than_n
