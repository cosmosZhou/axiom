from util import *


@apply
def apply(given, right_open=False):
    a, b = given.of(LessEqual)
    return Subset(Interval(-oo, a, right_open=right_open), Interval(-oo, b, right_open=right_open))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    t = Symbol(real=True)
    Eq << Set.Subset.given.All_Mem.apply(Eq[1], t)

    Eq << Eq[-1].this.expr.simplify()

    Eq << ~Eq[-1]

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.expr.apply(Algebra.Gt.of.Gt.Le)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2020-11-23
