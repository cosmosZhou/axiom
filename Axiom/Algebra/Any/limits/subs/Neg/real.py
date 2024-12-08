from util import *


@apply
def apply(self, old, new):
    from Axiom.Algebra.All.limits.subs.Neg.real import limits_subs
    return limits_subs(Any, self, old, new)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b, c = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Any[x:Interval(a, b, right_open=True)](f(x) > 0), x, c - x)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Any.to.Any.limits.subs.Neg.real, x, c - x)
    Eq << Eq[-1].this.rhs.apply(Algebra.Any.to.Any.limits.subs.Neg.real, x, c - x)


if __name__ == '__main__':
    run()
# created on 2019-02-20
