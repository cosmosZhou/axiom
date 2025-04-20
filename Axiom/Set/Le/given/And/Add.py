from util import *


@apply(simplify=False)
def apply(given, t):
    a, b = given.of(LessEqual)

    return LessEqual(a + t, b + t), Element(t, Interval(-oo, oo))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    a, b = Symbol(real=True, given=True)
    t = Symbol(hyper_real=True, given=True)
    Eq << apply(a <= b, t)

    Eq << Set.Any.Eq.of.Mem.apply(Eq[2])

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[1], Eq[-1], simplify=None)
    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subs)



if __name__ == '__main__':
    run()
# created on 2021-05-19
