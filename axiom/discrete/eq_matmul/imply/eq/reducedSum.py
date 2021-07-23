from util import *


@apply
def apply(given):
    (x, w), y = given.of(Equal[MatMul])
    [n] = x.shape
    _n, i, j = w.of(Swap)
    assert n == _n
    assert i >= 0 and i < n
    assert j >= 0 and j < n
    return Equal(ReducedSum(x), ReducedSum(y))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(n,), real=True, given=True)
    y = Symbol.y(shape=(n,), real=True, given=True)
    i = Symbol.i(domain=Range(0, n))
    j = Symbol.j(domain=Range(0, n))
    Eq << apply(Equal(x @ Swap(n, i, j), y))

    t = Symbol.t(integer=True)
    Eq << Eq[0][t].reversed

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[1].this.rhs.apply(algebra.reducedSum.to.sum, t)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum, t)

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()