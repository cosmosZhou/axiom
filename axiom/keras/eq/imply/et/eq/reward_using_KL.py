from util import *


@apply
def apply(eq):
    (r, t), (((S[t], n), r_human), kl) = eq.of(Equal[Indexed, Add[KroneckerDelta[Symbol - 1] * Symbol]])
    (((((a, S[t]), S[a[t].var]), ((s, S[t]), S[s[t].var])), (θ,)), ((S[a[t].as_boolean()], S[s[t].as_boolean()]), (θ_quote,))), β = kl.of(-Log[Probability[Conditioned[Equal[Indexed], Equal[Indexed]]] / Probability[Conditioned]] * Symbol)
    return Infer(t < n - 1, Equal(r[t], kl)), Equal(r[n - 1], kl._subs(t, n - 1) + r_human)


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, b, D = Symbol(integer=True, positive=True)
    #n is the sequence length
    #b is the hidden embedding size of the state
    #D is the total size of the traininable weights
    s = Symbol(shape=(n, b), real=True, random=True) #states / observation
    a = Symbol(shape=(n,), integer=True, random=True) #actions
    r = Symbol(shape=(n,), real=True) #rewards
    R_human = Symbol(real=True) #human reward
    θ, SFT = Symbol(shape=(D,), real=True)
    #θ is the trainable weights for the reinforcement-learning model
    #SFT is the untrainable weights for supervised fine-tuning model
    β = Symbol(real=True) #β is the constant to control the KL penalty
    t = Symbol(integer=True) #time step counter
    Eq << apply(Equal(r[t], -log(Probability[θ](a[t] | s[t]) / Probability[SFT](a[t] | s[t])) * β + KroneckerDelta(t, n - 1) * R_human))

    Eq << Eq[0].this.find(KroneckerDelta).apply(algebra.delta.to.piece)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul.to.piece, simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piece)

    Eq << algebra.cond_piece.imply.et.infer.apply(Eq[-1])

    Eq << Eq[-2].subs(t, n - 1)

    Eq << algebra.infer.imply.infer.et.domain_defined.apply(Eq[-1], t)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.given.et)

    Eq << Eq[-1].this(t).find(GreaterEqual).simplify()

    Eq << Eq[-1].this.find(And).apply(algebra.ne.lt.given.lt)

    #https://arxiv.org/pdf/1909.08593.pdf#page=3




if __name__ == '__main__':
    run()
# created on 2023-04-13
# updated on 2023-06-06
