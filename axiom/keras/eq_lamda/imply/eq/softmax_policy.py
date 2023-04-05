from util import *


@apply
def apply(eq_given):
    ((((a, S[a.var]), (s, S[s.var])), [S[a], θ]), (S[a.var], S[0], m)), (phi_s, S[θ]) = eq_given.of(Equal[Lamda[Probability[Conditioned[Equal[2]]]], Softmax[MatMul]])
    return Equal(
        Derivative[θ](log(Probability[a:θ](a | s))),
        (phi_s[a.var] - Expectation[a:θ](phi_s[a], given=s)))


@prove
def prove(Eq):
    from axiom import stats, algebra, calculus

    m, n = Symbol(integer=True, positive=True)
    φ = Function(real=True, shape=(m, n))
    θ = Symbol(real=True, shape=(n,))
    s, a = Symbol(integer=True, random=True)
    Eq << apply(Equal(Lamda[a.var:m](Probability[a:θ](a | s)), softmax(φ(s.var) @ θ)))

    Eq << Eq[1].this.find(Expectation).apply(stats.expect.to.sum)

    a = a.var
    Eq << Eq[0][a]

    Eq << algebra.eq.imply.eq.log.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.log.to.add)

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], [θ])

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].this.find(Derivative[MatMul]).apply(calculus.grad.to.expr.st.poly.simple)

    Eq << Eq[-1].this.find(Derivative[ReducedSum]).apply(calculus.grad.to.reducedSum)

    Eq << Eq[-1].this.find(Derivative[MatMul]).apply(calculus.grad.to.expr.st.poly.simple)

    Eq << Eq[-1].this.find(ReducedSum).apply(algebra.reducedSum.to.sum, a)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.sum.absorb, 1)

    Eq << Eq[3] * Eq[3].find(ReducedSum)

    Eq << Eq[-2].subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2023-03-18
# updated on 2023-03-24
