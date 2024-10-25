from util import *


@apply
def apply(eq_x_bar, eq_M2):
    (x_bar, n), ((x, (S[0], S[n])), S[n]) = eq_x_bar.of(Equal[Indexed, ReducedSum[Sliced] / Symbol])
    (diff, limit), Mn2 = eq_M2.of(Equal[Sum[Expr ** 2]])
    k, S[0], S[n] = limit
    S[x[k]], S[x_bar[n]] = diff.of(Expr - Expr)
    return Equal(Difference[n](Mn2), (x[n] - x_bar[n + 1]) * (x[n] - x_bar[n]))


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    x_bar = Symbol(r"\bar {x}", real=True, shape=(oo,))
    Eq << apply(Equal(x_bar[n], ReducedSum(x[:n]) / n), Equal(M[n] ** 2, Sum[k:n]((x[k] - x_bar[n]) ** 2)))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[1].subs(n, n + 1) - Eq[1]

    Eq << Eq[-1].this(n).find(Sum).apply(algebra.sum.to.add.pop)

    Eq << algebra.eq_reducedSum.then.eq.sum.square.to.add.sum.square.apply(Eq[0], x_bar[n + 1], k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.eq_reducedSum.then.eq.add.square.to.mul.apply(Eq[0])

    Eq << algebra.eq.eq.then.eq.trans.apply(*Eq[-2:])




if __name__ == '__main__':
    run()
# created on 2023-11-07

from . import biased
from . import unbiased
