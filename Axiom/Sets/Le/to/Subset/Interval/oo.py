from util import *


@apply
def apply(given, left_open=False):
    a, b = given.of(LessEqual)
    return Subset(Interval(b, oo, left_open=left_open), Interval(a, oo, left_open=left_open))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    t = Symbol(real=True)
    Eq << Sets.Subset.of.All_In.apply(Eq[1], t)

    Eq << Eq[-1].this.expr.simplify()

    Eq << ~Eq[-1]

    Eq << Algebra.Any.to.Any.And.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.expr.apply(Algebra.Lt.Ge.to.Gt.trans)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-02-26
