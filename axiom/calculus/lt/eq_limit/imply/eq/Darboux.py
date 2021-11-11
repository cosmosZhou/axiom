from util import *


@apply
def apply(lt, eq, n=None, k=None):
    a, b = lt.of(Less)
    (M, (n, oo, dir)), (m, (_n, _oo, _dir)) = eq.of(Equal[Limit, Limit])
    assert n == _n
    assert oo == _oo == S.Infinity
    assert dir == _dir == -1
    M = M.of(Sum[Maxima, Tuple[0]] / Expr)    
    m = m.of(Sum[Minima, Tuple[0]] / Expr)
    assert M == m
    ((fx, (x, A, B)), (k, _n)), __n = M
    assert _n == n == __n
    p = A.as_poly(k)
    assert a == p.nth(0)
    assert b == p.nth(1) * n + a
    p = B.as_poly(k)
    assert ((b - a) / n - (p.nth(0) - a)).expand() == 0
    assert (b - a) / n - p.nth(1) == 0
    
    return Equal(Integral[x:a:b](fx), (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove(provable=False)
def prove(Eq):
    x, a, b = Symbol(real=True)
    f = Function(real=True)
    n, k = Symbol(integer=True)
    Eq << apply(a < b, Equal(Limit[n:oo](Sum[k:n](Maxima[x:a + (b - a) * k / n:a + (b - a) * (k + 1) / n](f(x))) / n), Limit[n:oo](Sum[k:n](Minima[x:a + (b - a) * k / n:a + (b - a) * (k + 1) / n](f(x))) / n)))


if __name__ == '__main__':
    run()
# created on 2020-05-27
# updated on 2020-05-27
