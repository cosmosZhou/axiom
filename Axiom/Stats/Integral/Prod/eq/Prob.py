from util import *


@apply
def apply(self):
    (((s, S[0]), S[s[0].var]), ((((S[s], t), S[s[t + 1].var]), S[s[t].as_boolean()]), (S[t], S[0], n))), (S[s[:n].var],) = self.of(Integral[Probability[Equal[Indexed]] * Product[Probability[Conditioned[Equal[Indexed[Symbol, Expr + 1]]]]]])

    return Equal(self, Probability(s[n]))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Stats

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    t = Symbol(integer=True) # time step counter
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq.hypothesis = apply(Integral[s[:n].var](Probability(s[0]) * Product[t:n](Probability(s[t + 1] | s[t]))))

    Eq << Eq.hypothesis.subs(n, 0)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Calculus.Integral.limits.pop.Slice)

    Eq << Eq[-1].this.find(Product).apply(Algebra.Prod.eq.Mul.pop)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].subs(Eq.hypothesis)

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(Stats.Prob.eq.Div.Prob.bayes)

    Eq << Eq[-1].this.lhs.apply(Stats.Integral.eq.Prob.marginal)


    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << Algebra.Imply.to.Eq.induct.apply(Eq[-1], n=n, start=0)



if __name__ == '__main__':
    run()
# created on 2023-04-04
