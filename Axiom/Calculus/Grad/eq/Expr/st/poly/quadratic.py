from util import *


@apply
def apply(self):
    (x, A, S[x]), (S[x], S[1]) = self.of(Derivative[MatMul])
    assert x.shape
    return Equal(self, (A + A.T) @ x)


@prove
def prove(Eq):
    from Axiom import Discrete, Calculus, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    A = Symbol(real=True, shape=(n, n))
    Eq << apply(Derivative[x](x @ A @ x))

    Eq << MatMul(*Eq[-1].lhs.find(MatMul).args[:2]).this.apply(Discrete.Dot.eq.Lamda, var={'k', 'j'})

    Eq << Eq[-1] @ x

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Sum)

    Eq << Eq[0].lhs.this.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Lamda)

    Eq << Eq[-1].this.rhs.find(Derivative).apply(Calculus.Grad.eq.Sum)

    Eq << Eq[-1].this.rhs.find(Derivative).apply(Calculus.Grad.eq.Sum)

    Eq << Eq[-1].this.find(Lamda).apply(Discrete.Lamda.eq.Dot)

    Eq << Eq[-1].this.find(Lamda).apply(Discrete.Lamda.eq.Dot)

    Eq << Eq[-1].this.find(Lamda).apply(Discrete.Lamda.eq.Dot)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.eq.Identity)

    Eq << Eq[-1].this.find(Add).apply(Discrete.Add.eq.Dot)



if __name__ == '__main__':
    run()
# created on 2021-12-25
# updated on 2021-12-26