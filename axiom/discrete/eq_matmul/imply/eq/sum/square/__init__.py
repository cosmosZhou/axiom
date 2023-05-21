from util import *


@apply
def apply(given, i=None):
    (x, w), y = given.of(Equal[MatMul])
    n, = x.shape
    _i, _j = w.of(SwapMatrix)    
    assert 0 <= _i < n
    assert 0 <= _j < n
    if i is None:
        i = given.generate_var(integer=True, var='i')

    return Equal(Sum[i:n](x[i]**2), Sum[i:n](y[i]**2))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True, given=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y))

    Eq << discrete.eq_matmul.eq_matmul.imply.eq.sum.apply(Eq[0], Eq[0])




























if __name__ == '__main__':
    run()

from . import double_limits
from . import offset
# created on 2019-11-13
