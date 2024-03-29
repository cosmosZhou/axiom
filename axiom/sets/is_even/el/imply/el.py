from util import *


@apply
def apply(is_even, contains_n):
    n = is_even.of(Equal[Expr % 2, 0])
    S[n], ab = contains_n.of(Element)

    a, b = ab.of(Range)
    b -= 1

    return Element(n, imageset(n, 2 * n, Range((a + 1) // 2, b // 2 + 1)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b, n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0), Element(n, Range(a, b + 1)))

    Eq << algebra.is_even.imply.any.apply(Eq[0])

    Eq << algebra.cond.any.imply.any.et.apply(Eq[1], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, ret=0)

    Eq << Eq[-1].this.find(Element).apply(sets.el.imply.el.div.range, 2, simplify=None)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.imply.eq.div, 2, simplify=None)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.imply.eq.reverse, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.ceiling.to.floor)

    S = Symbol(conditionset(n, Eq[-1]))
    Eq << S.this.definition

    Eq << Eq[-1].this.rhs.limits_subs(n, 2 * n)

    Eq << Element(n, S, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].subs(Eq[-2])

    


if __name__ == '__main__':
    run()

# created on 2018-05-26
# updated on 2023-11-11
