from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.All.limits.subs.Neg.real import limits_subs
    return limits_subs(All, self, old, new)


@prove
def prove(Eq):
    from Axiom import Algebra, Set

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << Algebra.Or.of.All.subs.apply(Eq[0], x, c - x)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotMem.Neg.of.NotMem)

    Eq << Eq[-1].this.find(NotElement).apply(Set.NotMem.Add.of.NotMem, c)

    Eq << Algebra.All.of.Or.apply(Eq[-1], pivot=1, wrt=x)





if __name__ == '__main__':
    run()
# created on 2018-12-15
# updated on 2023-05-13
