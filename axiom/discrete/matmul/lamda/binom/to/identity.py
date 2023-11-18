from util import *


@apply
def apply(self):
    (((i, j), j_limit, i_limit), (((S[i], S[j]), exp), S[j_limit], S[i_limit])) = self.of(Lamda[Binomial] @ Lamda[Binomial * (-1) ** Expr])
    S[j], S[0], n = j_limit
    S[i], S[0], S[n] = i_limit
    assert exp in (j - i, j + i)
    return Equal(self, Identity(n))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Lamda[j:n, i:n](Binomial(i, j)) @ Lamda[j:n, i:n]((-1) ** (j - i) * Binomial(i, j)))

    Eq << Eq[0].this.lhs.apply(discrete.matmul.to.lamda)

    k = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.split, cond=k <= i)

    Eq << Eq[-1].this.lhs().find(Min).simplify()

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.mul.binom.to.delta)
    Eq << Eq[-1].this.lhs.apply(algebra.lamda.delta.to.identity)



if __name__ == '__main__':
    run()
# created on 2023-08-27
