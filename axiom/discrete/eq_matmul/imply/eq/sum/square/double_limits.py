from util import *


@apply
def apply(given, i=None, j=None):
    (x, w), y = given.of(Equal[MatMul])
    [n] = x.shape
    _n, _i, _j = w.of(Swap)
    assert n == _n
    assert _i >= 0 and _i < n
    assert _j >= 0 and _j < n
    if i is None:
        i = given.generate_var(integer=True, var='i')
    if j is None:
        j = given.generate_var(excludes=i, integer=True, var='j')

    return Equal(Sum[j:i, i:n]((x[i] - x[j])**2), Sum[j:i, i:n]((y[i] - y[j])**2))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(n,), real=True, given=True)
    y = Symbol.y(shape=(n,), real=True, given=True)
    i = Symbol.i(domain=Range(0, n))
    j = Symbol.j(domain=Range(0, n))
    Eq << apply(Equal(x @ Swap(n, i, j), y))

    j, i = Eq[1].lhs.variables
    Eq << Eq[1].this.lhs.apply(algebra.sum_square.to.add.st.double_limits)

    Eq << Eq[-1].this.rhs.apply(algebra.sum_square.to.add.st.double_limits)

    Eq << discrete.eq_matmul.imply.eq.sum.apply(Eq[0], i)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Pow[~Sum]).simplify()

    Eq << discrete.eq_matmul.imply.eq.sum.square.apply(Eq[0])
    Eq << Eq[-1].this.lhs.simplify()
    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()