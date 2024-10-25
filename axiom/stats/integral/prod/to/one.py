from util import *


@apply
def apply(self):
    ((((s, t), S[s[t + 1].var]), S[s[t].as_boolean()]), (S[t], S[0], n)), (S[s[1:n + 1].var],) = self.of(Integral[Product[Probability[Conditioned[Equal[Indexed[Symbol, Expr + 1]]]]]])
    return Equal(self, 1)


@prove
def prove(Eq):
    from axiom import calculus, algebra, stats

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    t = Symbol(integer=True) # time step counter
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq.hypothesis = apply(Integral[s[1:n + 1].var](Product[t:n](Probability(s[t + 1] | s[t]))))

    Eq << Eq.hypothesis.subs(n, 0)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(calculus.integral.limits.pop.slice)

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.pop)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.limits.swap)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Probability]).apply(stats.integral.to.one.conditioned)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << algebra.infer.then.eq.induct.apply(Eq[-1], n=n, start=0)



if __name__ == '__main__':
    run()
# created on 2023-04-03
