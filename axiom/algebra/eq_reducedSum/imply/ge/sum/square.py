from util import *


@apply
def apply(eq_x_bar, t, k=None):
    ((x, (S[0], n)), S[n]), x_bar = eq_x_bar.of(Equal[ReducedSum[Sliced] / Symbol])
    if k is None:
        k = eq_x_bar.generate_var(integer=True, var='k', excludes=t.free_symbols)
    return Sum[k:n]((x[k] - t) ** 2) >= Sum[k:n]((x[k] - x_bar) ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, shape=(oo,))
    n, k = Symbol(integer=True)
    t = Symbol(real=True)
    x_bar = Symbol(r"{\bar {x}}", real=True)
    Eq << apply(Equal(x_bar, ReducedSum(x[:n]) / n), t, k)

    Eq << algebra.eq_reducedSum.imply.eq.sum.square.to.add.sum.square.apply(Eq[0], t, k)

    Eq << GreaterEqual(Eq[-1].rhs.find(Add ** 2), 0, plausible=True)

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[0])

    Eq << algebra.et.imply.cond.apply(Eq[-1], 1).reversed

    Eq << algebra.gt_zero.ge.imply.ge.mul.apply(Eq[-1], Eq[-3])

    Eq << algebra.ge.eq.imply.ge.add.apply(Eq[-1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2023-11-06
