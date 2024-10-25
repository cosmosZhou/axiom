from util import *


@apply
def apply(self, old, new):
    from axiom.algebra.all.limits.subs.negate.real import limits_subs
    return limits_subs(All, self, old, new)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << algebra.all.then.ou.subs.apply(Eq[0], x, c - x)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.then.notin.neg)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.then.notin.add, c)

    Eq << algebra.ou.then.all.apply(Eq[-1], pivot=1, wrt=x)





if __name__ == '__main__':
    run()
# created on 2018-12-15
# updated on 2023-05-13
