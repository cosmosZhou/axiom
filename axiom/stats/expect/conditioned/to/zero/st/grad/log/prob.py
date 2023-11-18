from util import *


@apply
def apply(self):
    (grad, given), (x_expect, θ) = self.of(Expectation[Conditioned])
    ((((x, S[x.surrogate]), S[given]), [x_prob, S[θ]]), (S[θ], S[1])) = grad.of(Derivative[Log[Probability[Conditioned[Equal]]]])
    assert x_prob.index_contains(x)
    assert x_expect.index_contains(x)
    return Equal(self, ZeroMatrix(*θ.shape))


@prove
def prove(Eq):
    from axiom import stats, calculus

    D, n = Symbol(integer=True, positive=True)
    #D denotes the size of the trainable weights
    x, s = Symbol(real=True, shape=(n,), random=True)
    θ = Symbol(real=True, shape=(D,))
    Eq << apply(Expectation[x:θ](Derivative[θ](log(Probability[x:θ](x.surrogate | s))) | s))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.lhs.apply(calculus.integral.to.grad)

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.one.conditioned)

    Eq << Eq[-1].this.lhs.doit()

    #https://spinningup.openai.com/en/latest/spinningup/rl_intro3.html#expected-grad-log-prob-lemma
    


if __name__ == '__main__':
    run()
# created on 2023-04-03
