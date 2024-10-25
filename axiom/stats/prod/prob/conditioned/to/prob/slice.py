from util import *


@apply
def apply(self):
    (((s, k), S[s[k].var]), S[s[:k].as_boolean()]), (S[k], S[0], n) = self.of(Product[Probability[Conditioned[Equal[Indexed]]]])
    return Equal(self, Probability(s[:n]), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, stats

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    n = Symbol(integer=True, nonnegative=True, given=False)  # total time step
    Eq << apply(Product[k:n](Probability(s[k] | s[:k])))


    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.pop)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(stats.prob.to.div.prob.bayes)

    Eq << Eq[-1].this.find(Equal & Equal).apply(algebra.eq.eq.to.eq.concat)

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq << algebra.infer.then.eq.induct.apply(Eq[-1], n=n, start=0)




if __name__ == '__main__':
    run()
# created on 2023-04-08
