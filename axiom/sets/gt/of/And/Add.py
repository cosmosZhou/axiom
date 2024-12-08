from util import *


@apply(simplify=False)
def apply(given, t):
    a, b = given.of(Greater)

    return Greater(a + t, b + t), Element(t, Interval(-oo, oo))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b = Symbol(real=True, given=True)
    t = Symbol(hyper_real=True, given=True)
    Eq << apply(a > b, t)

    Eq << Sets.In.to.Any.Eq.apply(Eq[2])

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[1], Eq[-1], simplify=None)
    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs)


if __name__ == '__main__':
    run()
# created on 2021-04-15
