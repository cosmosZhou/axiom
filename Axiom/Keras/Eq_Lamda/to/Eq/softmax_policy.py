from util import *


@apply
def apply(eq_given):
    ((((a, S[a.var]), (s, S[s.var])), [S[a], θ]), (S[a.var], S[0], m)), (phi_s, S[θ]) = eq_given.of(Equal[Lamda[Probability[Conditioned[Equal[2]]]], Softmax[MatMul]])
    return Equal(
        Derivative[θ](log(Probability[a:θ](a | s))),
        (phi_s[a.var] - Expectation[a:θ](phi_s[a], given=s)))


@prove
def prove(Eq):
    from Axiom import Stats, Algebra, Calculus

    m, n = Symbol(integer=True, positive=True)
    φ = Function(real=True, shape=(m, n))
    θ = Symbol(real=True, shape=(n,))
    s, a = Symbol(integer=True, random=True)
    Eq << apply(Equal(Lamda[a.var:m](Probability[a:θ](a | s)), softmax(φ(s.var) @ θ)))

    Eq << Eq[1].this.find(Expectation).apply(Stats.Expect.eq.Sum)

    a = a.var
    Eq << Eq[0][a]

    Eq << Algebra.Eq.to.Eq.Log.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Log.eq.Add)

    Eq << Calculus.Eq.to.Eq.Grad.apply(Eq[-1], [θ])

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.find(Derivative[MatMul]).apply(Calculus.Grad.eq.Expr.st.poly.simple)

    Eq << Eq[-1].this.find(Derivative[ReducedSum]).apply(Calculus.Grad.eq.ReducedSum)

    Eq << Eq[-1].this.find(Derivative[MatMul]).apply(Calculus.Grad.eq.Expr.st.poly.simple)

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum, a)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Algebra.Mul.Sum.absorb, 1)

    Eq << Eq[3] * Eq[3].find(ReducedSum)

    Eq << Eq[-2].subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2023-03-18
# updated on 2023-03-24
