from util import *


@apply
def apply(ne_zero, gt):
    m, n = gt.of(Greater)
    assert m > 0 and n > 0
    args = ne_zero.of(Unequal[Probability[Equal], 0])
    if args[-1].is_Tuple:
        (x, x_var), *weights = args
    else:
        x, x_var = args
        weights = []

    S[m], *_ = x.shape

    return Unequal(Probability(Equal(x[:n], x_var[:n]), *weights), 0), Unequal(Probability(Equal(x[n:m], x_var[n:m]), *weights), 0)

@prove
def prove(Eq):
    from Axiom import Algebra, Stats

    m, n = Symbol(integer=True, positive=True)
    x = Symbol(random=True, real=True, shape=(oo,))
    Eq << apply(Unequal(Probability(x[:m]), 0),
                m > n)

    Eq << Algebra.Gt.to.Iff.split.Eq.apply(Eq[1], *Eq[0].lhs.arg.args)

    Eq << Algebra.Iff.Cond.to.Cond.subs.apply(Eq[-1], Eq[0])

    Eq << Stats.Ne_0.to.And.Ne_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-03-26
