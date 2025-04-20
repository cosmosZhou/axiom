from util import *


def extract(p_polynomial, x, y):
    assert x.shape == y.shape
    n, = p_polynomial.shape
    (b, e), (k, *_) = p_polynomial.of(Lamda[FallingFactorial])

    assert not b.has(k)
    assert not b.is_given
    assert not x._has(b) and not y._has(b)
    assert e.as_poly(k).degree() == 1
    return x, y

@apply
def apply(given):
    (p, x), (S[p], y) = given.of(Equal[MatMul[2]])
    return Equal(*extract(p, x, y))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    p = Symbol(complex=True)
    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    x, y = Symbol(shape=(n,), complex=True, given=True)
    Eq << apply(Equal(Lamda[k:n](FallingFactorial(p, k)) @ x, Lamda[k:n](FallingFactorial(p, k)) @ y))

    i = Symbol(domain=Range(n))
    Eq << Eq[0].subs(p, i)

    Eq << Algebra.All.of.Cond.apply(Eq[-1], i)

    Eq << Algebra.EqLamda.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Discrete.Lamda.Dot.eq.Dot)

    Eq << Eq[-1].this.rhs.apply(Discrete.Lamda.Dot.eq.Dot)

    Eq.statement = Eq[-1].T

    Eq << Det(Eq.statement.find(Lamda)).this.doit()

    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << Discrete.EqDot.of.Ne_0.Eq.apply(Eq[-1], Eq.statement)





if __name__ == '__main__':
    run()
# created on 2023-08-26
# updated on 2023-08-27
