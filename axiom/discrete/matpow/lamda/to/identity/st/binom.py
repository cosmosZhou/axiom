from util import *


@apply
def apply(self):
    ((i, j), exp), (S[j], S[0], n), (S[i], S[0], S[n]) = self.of(MatPow[Lamda[Binomial * (-1) ** Expr], 2])
    assert exp in (i, j)
    return Equal(self, Identity(n))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Lamda[j:n, i:n]((-1) ** j * Binomial(i, j)) ^ 2)

    A, B = Symbol(Eq[0].find(Lamda))
    Eq << (A @ B).this.apply(discrete.matmul.to.lamda)

    Eq << A.this.definition

    Eq << B.this.definition

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    k = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.split, cond=k <= i)

    Eq << Eq[-1].this.rhs().find(Min).simplify()

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.mul.binom.to.delta)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.delta.to.identity)




if __name__ == '__main__':
    run()
# created on 2023-08-27
