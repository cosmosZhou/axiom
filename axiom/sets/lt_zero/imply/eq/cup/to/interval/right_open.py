from util import *


@apply
def apply(is_nonnegative, k=None):
    n = is_nonnegative.of(Expr < 0)
    assert n.is_integer
    if k is None:
        k = is_nonnegative.generate_var(integer=True)
    return Equal(Cup[k:n:0](Interval(k, k + 1, right_open=True)), Interval(n, 0, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n, k = Symbol(integer=True)
    Eq << apply(n < 0, k)

    m = Symbol(integer=True, nonpositive=True)
    Eq << sets.cup.to.interval.right_open.negative.apply(Cup[k:m:0](Eq[1].lhs.expr))

    Eq << Eq[-1].subs(m, n)

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.cond.apply(Eq[-1], 0)

    


if __name__ == '__main__':
    run()
# created on 2021-02-20
# updated on 2023-05-20
