from util import *


def markov_assumptions(s, a, r):
    # d is the number of output actions
    # L + 1 is the length of the states
    L, = a.shape
    S[L + 1], b = s.shape
    [S[L]] = r.shape

    k = Symbol(domain=Range(1, L))
    given = s[:k] & a[:k] & r[:k]
    return Equal(s[k + 1] | given, s[k + 1]), Equal(a[k] | given, a[k]), Equal(r[k] | given, r[k]), Unequal(Probability(s, a, r), 0)


def process_assumptions(s_independence_assumption, a_independence_assumption, r_independence_assumption):
    regex = Equal[Conditioned[Indexed, Equal & Equal & Equal], Expr]
    if a_independence_assumption.rhs.is_Probability:
        ((ak, given), aθ), (S[ak], S[aθ]) = a_independence_assumption.of(Equal[Probability[Conditioned[Equal, Equal & Equal & Equal]], Probability[Equal]])
        ((r, k), S[given]), S[r[k]] = r_independence_assumption.of(regex)
        ((s, S[k + 1]), S[given]), S[s[k + 1]] = s_independence_assumption.of(regex)

        ak, S[ak.var] = ak
        a, k = ak.of(Indexed)

        (S[a[:k]], S[a.var[:k]]), (S[r[:k]], S[r.var[:k]]), (S[s[:k]], S[s.var[:k]]) = given
        S[a], θ = aθ
        return s, a, r, (a, θ)
    else:
        ((a, k), given), S[a[k]] = a_independence_assumption.of(regex)
        ((r, S[k]), S[given]), S[r[k]] = r_independence_assumption.of(regex)
        ((s, S[k + 1]), S[given]), S[s[k + 1]] = s_independence_assumption.of(regex)

        (S[a[:k]], S[a.var[:k]]), (S[r[:k]], S[r.var[:k]]), (S[s[:k]], S[s.var[:k]]) = given

        return s, a, r



@apply
def apply(s_independence_assumption, a_independence_assumption, r_independence_assumption, ne, t=None, i=None):
    s, a, r, *weights = process_assumptions(s_independence_assumption, a_independence_assumption, r_independence_assumption)
    S[Probability(s, a, r, *weights)] = ne.of(Unequal[0])

    L, = r.shape

    if i is None:
        i = Symbol(integer=True)

    if t is None:
        t = Symbol(integer=True, domain=Range(L))

    assert t < L
    return Equal(Probability(s[:t + 1], a[:t], r[:t], *weights),
                 Probability(s[0], *weights) * Product[i:t](Probability(a[i] | s[i], *weights) * Probability(s[i + 1] & r[i], given=s[i] & a[i], *weights)))


@prove
def prove(Eq):
    from axiom import stats, algebra

    b, d, L = Symbol(domain=Range(2, oo))
    s = Symbol(shape=(L + 1, b), real=True, random=True)
    a = Symbol(shape=(L,), domain=Range(d), random=True)
    r = Symbol(shape=(L,), real=True, random=True)
    T = Symbol(integer=True, domain=Range(1, L))
    t = Symbol(integer=True)
    Eq << apply(*markov_assumptions(s, a, r), T, t)

    a, k = Eq[1].rhs.of(Indexed)
    Eq.ne_zero = stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[3], [slice(0, k), slice(0, k), slice(0, k + 1)])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq.ne_zero, s[k + 1], a[k], r[k])

    Eq << Eq[-1].this.lhs.arg.apply(algebra.et.concat, i=3, j=0)

    Eq << Eq[-1].this.lhs.arg.apply(algebra.et.concat, i=3, j=0)

    Eq << Eq[-1].this.lhs.arg.apply(algebra.et.concat, i=3, j=0)

    Eq.recursion = algebra.ne_zero.eq.imply.eq.scalar.apply(Eq.ne_zero, Eq[-1])

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[3], [slice(0, k + 1), slice(0, k), slice(0, k + 1)])

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.to.et.eq.split)

    Eq.ne_zero_sar = Eq[-1].this.find(Equal[4]).apply(algebra.eq.to.et.eq.split)

    Eq << stats.ne_zero.ne_zero.imply.ne_zero.conditioned.apply(Eq.ne_zero, Eq[-1])

    Eq << stats.ne_zero.imply.eq.bayes.conditioned.apply(Eq[-1], r[k], s[k + 1])

    Eq << Eq[-1].this.rhs.find(Conditioned).rhs.args[-1].apply(algebra.eq.to.et.eq.split)

    Eq << Eq[-1].this.find(Probability[2]).arg.rhs.args[-1].apply(algebra.eq.to.et.eq.split)

    Eq << Eq.ne_zero.this.find(Equal[3]).apply(algebra.eq.to.et.eq.split)

    Eq << stats.ne_zero.eq_conditioned.imply.eq.conditioned.joint.apply(Eq[1], Eq[-1])

    Eq << Eq[-3].subs(Eq[-1])

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    Eq.ne_zero_a, Eq[-1] = stats.ne_zero.imply.et.ne_zero.apply(Eq[3], 1)

    Eq.ne_zero_r, Eq.ne_zero_s = stats.ne_zero.imply.et.ne_zero.apply(Eq[-1])

    Eq << stats.eq_conditioned.eq_conditioned.imply.eq.prob.joint.apply(Eq[0], Eq[2])

    Eq << stats.ne_zero.imply.ne_zero.conditioned.apply(Eq.ne_zero_sar, a[k], s[k])

    Eq << stats.ne_zero.eq.imply.eq.conditioned.joint.st.conditioned.apply(Eq[-2], Eq[-1])

    Eq.recursion = Eq.recursion.subs(Eq[-1])

    Eq << algebra.eq.imply.eq.prod.apply(Eq.recursion, (k, 1, T))

    Eq << Eq[-1].this.rhs.limits_subs(Eq[-1].rhs.variable, t)

    Eq << Eq[-1] * Eq[-1].find(Pow[~Probability])

    Eq << Eq[-1].this.rhs.find(Probability[~And]).args[-1].apply(algebra.eq.to.et.eq.split)

    Eq << stats.ne_zero.imply.ne_zero.slice.apply(Eq.ne_zero_s, 0)

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], a[0], r[0], s[1])

    Eq.final = Eq[-3].subs(Eq[-1])

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[3], slice(0, None, 2))[0]

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[-1], [0, 0])

    Eq << stats.ne_zero.imply.ne_zero.conditioned.apply(Eq[-1], s[0])

    Eq << stats.ne_zero.imply.eq.bayes.conditioned.apply(Eq[-1], r[0], s[1])

    Eq << Eq.final.subs(Eq[-1])

    Eq << Eq[4].this.find(Product).apply(algebra.prod.to.mul.shift)

    
    


if __name__ == '__main__':
    run()
# created on 2023-03-22
# updated on 2023-05-17
