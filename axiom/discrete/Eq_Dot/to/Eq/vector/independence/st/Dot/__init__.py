from util import *


def extract(p_polynomial, x, y):
    assert x.shape == y.shape
    n, = p_polynomial.shape

    if p_polynomial.is_Lamda:
        (b, e), (k, *_) = p_polynomial.of(Lamda[Pow])
    else:
        b, (e, (k, *_)) = p_polynomial.of(Pow[Lamda])

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

    p = Symbol(complex=True, zero=False)
    n, k = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), complex=True, given=True)
    Eq << apply(Equal(Lamda[k:n](p ** k) @ x, Lamda[k:n](p ** k) @ y))

    i = Symbol(domain=Range(1, n + 1))
    Eq << Eq[0].subs(p, i)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], i)

    Eq << Algebra.All_Eq.to.Eq.Lamda.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Discrete.Lamda.Dot.eq.Dot)

    Eq << Eq[-1].this.rhs.apply(Discrete.Lamda.Dot.eq.Dot)

    Eq << Eq[-1].T

    Eq << Eq[-1].this.find(Add[Lamda]).apply(Algebra.Add.eq.Lamda).this.find(Pow[Lamda]).apply(Algebra.Pow.eq.Lamda, simplify=None)

    Eq.statement = Eq[-1].this.find(Add[Lamda]).apply(Algebra.Add.eq.Lamda).this.find(Pow[Lamda]).apply(Algebra.Pow.eq.Lamda, simplify=None)

    i, k = Eq.statement.lhs.args[1].variables
    Eq << Discrete.Det.Lamda.eq.Prod.vandermonde.st.linear.apply(Det(Lamda[i:n, k:n]((i + 1) ** k)))

    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)



    Eq << Discrete.Ne_0.Eq.to.Eq.Dot.apply(Eq[-1], Eq.statement)





if __name__ == '__main__':
    run()
# created on 2020-08-21
# updated on 2023-08-27

del FallingFactorial
from . import FallingFactorial
