from util import *


@apply
def apply(given, i=None, j=None):
    (x, w), y = given.of(Equal[MatMul])
    n, = x.shape
    _i, _j = w.of(SwapMatrix)
    assert 0 <= _i < n
    assert 0 <= _j < n
    if i is None:
        i = given.generate_var(integer=True, var='i')
    if j is None:
        j = given.generate_var(excludes=i, integer=True, var='j')

    return Equal(Sum[j:i, i:n]((x[i] - x[j])**2), Sum[j:i, i:n]((y[i] - y[j])**2))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True, given=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y))

    j, i = Eq[1].lhs.variables
    Eq << Eq[1].this.lhs.apply(algebra.sum.square.to.add.st.double_limits)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.square.to.add.st.double_limits)

    Eq << discrete.eq_matmul.imply.eq.sum.apply(Eq[0], i)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].simplify()

    Eq << discrete.eq_matmul.imply.eq.sum.square.apply(Eq[0])









if __name__ == '__main__':
    run()
# created on 2019-11-14
# updated on 2023-05-06
