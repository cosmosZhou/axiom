from util import *


@apply
def apply(self):
    (a, b), (k, i, n) = self.of(Sum[Expr * (-1) ** Expr])
    n -= 1
    S[k], i = a.of(Stirling * Stirling1(n, k))
    assert b == k - i or b == k + i
    return Equal(self, KroneckerDelta(n, i))


@prove
def prove(Eq):
    k = Symbol(integer=True)
    i = Symbol(integer=True, nonnegative=True)
    n = Symbol(domain=Range(i, oo))
    Eq << apply(Sum[k:i:n + 1]((-1) ** (k - i) * Stirling1(n, k) * Stirling(k, i)))

    


if __name__ == '__main__':
    run()
# created on 2023-08-20
