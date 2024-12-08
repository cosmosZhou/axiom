from util import *


@apply
def apply(self):
    ((S1, j_limit, i_limit), (S2, S[j_limit], S[i_limit])) = self.of(Lamda @ Lamda)
    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    if isinstance(S1, Mul) and isinstance(S2, Mul):
        exp, S1 = S1.of((-1) ** Expr * Expr)
        S[exp], S2 = S2.of((-1) ** Expr * Expr)
        assert exp in (i, j)
    else:
        if isinstance(S1, (Stirling, Stirling1)):
            exp, S2 = S2.of((-1) ** Expr * Expr)
        elif isinstance(S2, (Stirling, Stirling1)):
            exp, S1 = S1.of((-1) ** Expr * Expr)

        assert exp in (j - i, j + i)
    assert {S1, S2} == {Stirling(i, j), Stirling1(i, j)}
    return Equal(self, Identity(n))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Lamda[j:n, i:n](Stirling(i, j)) @ Lamda[j:n, i:n]((-1) ** (j - i) * Stirling1(i, j)))

    Eq << Eq[0].this.lhs.apply(Discrete.Dot.eq.Lamda)

    k = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.split, cond=k <= i)

    Eq << Eq[-1].this.lhs().find(Min).simplify()

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Mul.Stirling.eq.Delta)

    Eq << Eq[-1].this.lhs.apply(Algebra.Lamda.Delta.eq.Identity)




if __name__ == '__main__':
    run()
# created on 2023-08-27
