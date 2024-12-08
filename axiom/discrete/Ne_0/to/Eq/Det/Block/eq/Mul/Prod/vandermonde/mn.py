from util import *


@apply
def apply(is_nonzero, x1, m, d):
    x2 = is_nonzero.of(Unequal[0])
    i, j = Symbol(integer=True)
    assert m > d
    return Equal(Det(BlockMatrix([Lamda[j:m, i:d](j ** i * x1 ** j), Lamda[j:m, i:m - d](j ** i * x2 ** j)])),
                 x2 ** Binomial(m - d, 2) * x1 ** Binomial(d, 2) * (x2 - x1) ** (d * (m - d)) * Product[i:d](factorial(i)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    d = Symbol(integer=True, positive=True)
    m = Symbol(domain=Range(d + 1, oo))
    x1, x2 = Symbol(complex=True)
    Eq << apply(Unequal(x2, 0), x1, m, d)

    Eq << Algebra.Ne_0.to.Ne_0.Div.apply(Eq[0])

    r = Symbol(Eq[-1].lhs * x1)
    Eq << r.this.definition * x2

    Eq << Eq[-1].reversed

    Eq << Eq[1].subs(Eq[-1])

    j, i = Eq[-1].find(Lamda[Tuple[2]]).variables
    Eq << (Eq[-1].lhs.arg @ Lamda[j:m, i:m](Eq[2].lhs ** j * KroneckerDelta(i, j))).this.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lamda.Piece.eq.Block)

    Eq << Discrete.Eq.to.Eq.Det.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Discrete.Det.Block.eq.Mul.Prod.vandermonde.st.Lamda.Pow.ratio)

    Eq << Eq[-1].subs(r.this.definition)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.eq.Mul)

    Eq << Eq[-1] * x2 ** binomial(m, 2)

    Eq << Eq[-1].this.lhs.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)

    Eq << Eq[-1].this.find(Symbol ** ~Add).expand()

    Eq << Eq[-1].this.rhs.find((~Add) ** Mul).apply(Algebra.Add.eq.Mul.together)

    Eq << Eq[-1].this.rhs.find(Mul ** Mul).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.rhs.find(Mul ** Binomial).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.find(Symbol ** Add).find(Binomial).apply(Discrete.Binom.eq.Add.st.two, d)




if __name__ == '__main__':
    run()
# created on 2022-07-11
