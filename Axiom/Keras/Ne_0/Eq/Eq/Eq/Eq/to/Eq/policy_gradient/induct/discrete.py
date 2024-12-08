from util import *


@apply
def apply(eq, Q_def, V_def, n=None):
    from Axiom.Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.And.Eq.Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    assert n >= 0
    return Equal(Derivative[π](V_st_var._subs(s[t].var, s[0].var)),
                 Sum[s[1:t + 1].var, t:n](γ ** t * (Product[t:t](Probability(s[t + 1] | s[t])) * Sum[a[t].var](Derivative[π](Probability[a:π](a[t] | s[t])) * Q_st_var))) + \
                 γ ** n * Sum[s[1:n + 1].var](Product[t:n](Probability(s[t + 1] | s[t])) * Derivative[π](V_st_var._subs(s[t].var, s[n].var))))


@prove
def prove(Eq):
    from Axiom import Keras, Algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), integer=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    n = Symbol(integer=True, nonnegative=True, given=False)
    *Eq[-3:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])), n)

    Eq.recursion = Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.Eq.Grad.policy_gradient.recursion.discrete.apply(*Eq[:3])

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Mul)

    Eq << Eq.recursion.subs(t, n)

    Eq << Eq.hypothesis.subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Sum[Add]).apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Symbol * Pow).powsimp()

    Eq << Eq[-1].this.find(Product * Sum[Mul[Probability]]).apply(Algebra.Mul.eq.Sum)

    Eq << Eq[-1].this.find(Probability * Product).args[1:].apply(Algebra.Mul.eq.Prod.limits.push)

    Eq << Eq[-1].this.find(Sum[Derivative * Product]).apply(Algebra.Sum.limits.concat)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Algebra.Imply.to.Eq.induct.apply(Eq[-1], n=n, start=0)

    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# bellman-equations
    # http://incompleteideas.net/book/bookdraft2017nov5.pdf (Page 47)
    # https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    # https://danieltakeshi.github.io/2017/04/02/notes-on-the-generalized-advantage-estimation-paper/
    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# id4
    # https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    # https://www.52coding.com.cn/tags/Reinforcement-Learning/
    # TRPO
    # https://arxiv.org/pdf/1502.05477.pdf




if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-05-20
