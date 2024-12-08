from util import *


@apply
def apply(ne_zero_A, ne_zero_B, ne_zero_AB):
    A = ne_zero_A.of(Unequal[Det, 0])
    B = ne_zero_B.of(Unequal[Det, 0])
    S[A + B] = ne_zero_AB.of(Unequal[Det, 0])
    return Equal(A @ ((A + B) ^ -1) @ B, ((A ^ -1) + (B ^ -1)) ^ -1)


@prove
def prove(Eq):
    from Axiom import Discrete

    n = Symbol(integer=True, positive=True)
    A = Symbol(r"\boldsymbol A", real=True, shape=(n, n))
    B = Symbol(r"\boldsymbol B", real=True, shape=(n, n))
    Eq << apply(Unequal(Det(A), 0), Unequal(Det(B), 0), Unequal(Det(A + B), 0))

    Eq << Discrete.Ne_0.to.Ne_0.Inv.apply(Eq[0])

    Eq << Discrete.Ne_0.to.Ne_0.Inv.apply(Eq[1])

    Eq << Discrete.Ne_0.to.Ne_0.Inv.apply(Eq[2])

    Eq << (A @ Eq[-1].lhs.arg @ B @ (Eq[-2].lhs.arg + Eq[-3].lhs.arg)).this.apply(Discrete.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.args[1].args[1:3].apply(Discrete.Dot.eq.Sub)

    Eq << Eq[-1].this.rhs.args[1].apply(Discrete.Dot.eq.Add)

    Eq << Eq[-1].this.rhs.args[1].apply(Discrete.Dot.eq.Add)

    Eq << Discrete.Eq_Dot.to.Eq.Inv.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-01
