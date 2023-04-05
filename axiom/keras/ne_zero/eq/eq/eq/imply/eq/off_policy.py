from util import *

from axiom.keras.ne_zero.eq.eq.eq.imply.eq.policy_gradient_theorem import markov_assumptions, process_assumptions

@apply
def apply(sar_independence_assumption, ne, pi_def, θ_quote):
    (s, s_var), (a, a_var), (r, r_var), θ = process_assumptions(sar_independence_assumption, ne)

    T, = r_var.shape
    (((at, S[at.var]), (st, S[st.var])), (S[a], S[θ],)), pi_θ = pi_def.of(Equal[Probability[Conditioned[Equal, Equal]]])
    S[a], t = at.of(Indexed)
    S[s], S[t] = st.of(Indexed)

    pi_θ = pi_θ._subs(a_var[t], a[t])
    pi_θ = pi_θ._subs(s_var[t], s[t])

    cond = s.surrogate & a.surrogate & r.surrogate
    return Equal(Derivative[θ](Expectation[s, a:θ, r](ReducedSum(r))),
                 Expectation[s, a:θ_quote, r](Probability[a:θ](cond) / Probability[a:θ_quote](cond) * ReducedSum(r) * Sum[t:T](Derivative[θ](log(pi_θ)))))


@prove
def prove(Eq):
    from axiom import keras, stats

    b, T, D = Symbol(domain=Range(2, oo))
    #T denotes the length of the episode
    #N denotes the number of sampling
    #D denotes the size of the trainable weights
    s = Symbol(shape=(T + 1, b), real=True, random=True)
    a = Symbol(shape=(T,), integer=True, random=True)
    r = Symbol(shape=(T,), real=True, random=True)
    t = Symbol(integer=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    pi = Function(real=True, shape=(), nonnegative=True)
    Eq << apply(*markov_assumptions(s, a, r, θ),
                Equal(Probability[a:θ](a[t] | s[t]), pi[θ](a.var[t], s.var[t])), θ_quote)

    Eq << keras.ne_zero.eq.eq.eq.imply.eq.expect.policy_gradient_theorem.apply(Eq[0], Eq[1], Eq[2])

    Eq << Eq[-1].this.rhs.apply(stats.expect.importance_sampling, θ_quote)




if __name__ == '__main__':
    run()
# created on 2023-03-24
# updated on 2023-03-28
