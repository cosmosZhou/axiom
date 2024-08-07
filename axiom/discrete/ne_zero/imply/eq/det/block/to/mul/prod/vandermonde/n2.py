from util import *


@apply
def apply(is_nonzero, n, x1):
    x2 = is_nonzero.of(Unequal[0])
    assert n >= 1
    i, j = Symbol(integer=True)
    return Equal(Det([Lamda[j:n + 2](x1 ** j), Lamda[j:n + 2](j * x1 ** j), Lamda[j:n + 2, i:n](j ** i * x2 ** j)]), x1 * x2 ** Binomial(n, 2) * (x2 - x1) ** (2 * n) * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    x1, x2 = Symbol(complex=True)
    Eq << apply(Unequal(x2, 0), n, x1)

    Eq << algebra.ne_zero.imply.ne_zero.div.apply(Eq[0])

    r = Symbol(Eq[-1].lhs * x1)
    Eq << r.this.definition * x2

    Eq << Eq[-1].reversed

    Eq.eq = Eq[1].subs(Eq[-1])

    Eq << Eq.eq.rhs.this.find(Add).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Mul ** Mul).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.rhs.find(Binomial).apply(discrete.binom.to.div.binom)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).expand()

    Eq << Eq.eq.subs(Eq[-1])

    j, i = Eq[-1].find(Lamda[Tuple[2]]).variables
    Eq << (Eq[-1].lhs.arg @ Lamda[j:n + 2, i:n + 2](Eq[2].lhs ** j * KroneckerDelta(i, j))).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.rhs.find(Mul ** Symbol).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.piece.to.block)

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.det.block.to.mul.prod.vandermonde.st.lamda.pow.n2)

    Eq << Eq[-1].subs(r.this.definition)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1] * x2 ** binomial(n, 2)

    Eq << Eq[-1].this.lhs.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.find(Symbol ** Add).expand()

    Eq << Eq[-1] * x2 ** (2 * n + 1)

    Eq << Eq[-1].this.rhs.find((~Add) ** Mul).apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.rhs.find(Mul ** Mul).apply(algebra.pow.to.mul.split.base)





if __name__ == '__main__':
    run()
# created on 2021-11-22
# updated on 2021-11-23