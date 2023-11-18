from util import *


@apply
def apply(eq, V_def, lt_dV, lt_V):
    from axiom.keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, V_st_var = extract_QVA(eq, None, V_def, None, lt_dV)

    S[V_st_var], [S[s[t].var]], [S[t]] = lt_V.of(Sup[Abs] < Infinity)

    At = γ ** Lamda[t](t) @ (r[t:] + γ * V_st_var._subs(s[t].var, s[t + 1:]) - V_st_var._subs(s[t].var, s[t:]))
    return Equal(γ ** Lamda[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 γ ** Lamda[t](t) @ Lamda[t](Expectation[r, a:π, s](Derivative[π](log(Probability[a:π](a[t].surrogate | s[t].surrogate))) * At)))


@prove
def prove(Eq):
    from axiom import discrete, algebra, calculus, stats, keras

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    π = Symbol(shape=(D,), real=True) #trainable weights for the agent
    t = Symbol(integer=True) #time step counter
    V = Function(real=True, shape=property(lambda self: self.arg.shape[:-1])) #State-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-4:], Eq.hypothesis = apply(Equal(r[t] | s[:t] & a[:t], r[t]), #history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Less(Sup[s[t].var, t](Abs(Derivative[π]((V[π] ^ γ)(s[t].var)))), oo),
                Less(Sup[s[t].var, t](Abs((V[π] ^ γ)(s[t].var))), oo))

    Eq.eq_matmul = Eq.hypothesis.find(Expectation, MatMul)._subs(s, s.var)._subs(r, r.var).this.apply(discrete.matmul.to.sum)

    k = Symbol(integer=True) #time step counter
    Eq << Eq.eq_matmul.rhs._subs(oo, k).this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Symbol * Pow).args[:2].apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs(t).find(Max).simplify()

    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (k, oo))

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.sum)

    Eq << Eq[-1].this.rhs.find(Limit).apply(calculus.limit.to.add)

    Eq.limit = Eq[-1].this.find(Limit[Sum]).apply(calculus.limit.to.sum)

    Eq << algebra.imply.all.le_sup.apply(Eq[3].lhs)

    Eq << Eq[-1].subs(t, t + k)

    Eq << algebra.cond.imply.all.apply(Eq[-1], k, simplify=None)

    Eq << algebra.all_le.imply.sup_le.apply(Eq[-1])

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[3])

    Eq << Less(Abs(γ, evaluate=False), 1, plausible=True)

    Eq << Eq[-1].this.lhs.doit()

    Eq << calculus.abs_lt.is_finite.imply.is_zero.limit.apply(Eq[-2], Eq[-1])

    Eq << Eq.limit.subs(Eq[-1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.eq_matmul, Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(algebra.lamda.to.pow)

    Eq << Eq[-1].this.rhs.find(Lamda).limits_subs(Eq[-1].rhs.find(Lamda).variable, t)

    Eq << Eq[-1].subs(s.var, s).subs(r.var, r)

    Eq << Eq.hypothesis.subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(stats.expect.to.mul)

    Eq << Eq[-1].find(-~Expectation).this.apply(stats.expect.law_of_iterated_expectation, s[t])

    Eq << Eq[-1].this.find(Expectation[~Expectation]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(Mul[~Expectation]).apply(stats.expect.conditioned.to.zero.st.grad.log.prob)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[2].subs(Eq[1])

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.matmul.to.matmul.grad)

    Eq << keras.eq_conditioned.is_finite.imply.eq.matmul.grad.expect.policy_gradient_theorem.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.rhs.find(Expectation).simplify()

    #https://arxiv.org/pdf/1506.02438.pdf#page=4




if __name__ == '__main__':
    run()
# created on 2023-04-13
# updated on 2023-05-20
