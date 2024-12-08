from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.All.limits.subs.Neg.real import limits_subs
    return limits_subs(Any, self, old, new)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Any[x:Interval(a, b, left_open=True)](f(x) > 0), x, c - x)

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[0], simplify=None)

    Eq << Algebra.Any.to.Any.limits.Neg.oo.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(Sets.In.to.In.Neg)

    Eq << Algebra.Any.to.Any.limits.subs.offset.apply(Eq[-1], -c)


if __name__ == '__main__':
    run()
# created on 2019-02-17
