from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.All.limits.subs.Neg.real import limits_subs
    return limits_subs(All, self, old, new)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << Algebra.All.to.Or.subs.apply(Eq[0], x, c - x)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn.to.NotIn.Neg)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn.to.NotIn.Add, c)

    Eq << Algebra.Or.to.All.apply(Eq[-1], pivot=1, wrt=x)





if __name__ == '__main__':
    run()
# created on 2018-12-15
# updated on 2023-05-13
