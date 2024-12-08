from util import *


@apply
def apply(self):
    grad, (x, θ) = self.of(Expectation)
    (((S[x], S[x.surrogate]), [S[x], S[θ]]), (S[θ], S[1])) = grad.of(Derivative[Log[Probability[Equal]]])
    return Equal(self, ZeroMatrix(*θ.shape))


@prove
def prove(Eq):
    from Axiom import Stats, Calculus

    D, n = Symbol(integer=True, positive=True)
    # D denotes the size of the trainable weights
    x = Symbol(real=True, shape=(n,), random=True)
    θ = Symbol(real=True, shape=(D,))
    Eq << apply(Expectation[x:θ](Derivative[θ](log(Probability[x:θ](Equal(x, x.surrogate))))))

    Eq << Eq[-1].this.lhs.apply(Stats.Expect.eq.Integral)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.eq.Grad)

    Eq << Eq[-1].this.find(Integral).apply(Stats.Integral.eq.One)

    Eq << Eq[-1].this.lhs.doit()

    # https://spinningup.openai.com/en/latest/spinningup/rl_intro3.html# expected-grad-log-prob-lemma




if __name__ == '__main__':
    run()
# created on 2023-03-26
# updated on 2023-04-03
