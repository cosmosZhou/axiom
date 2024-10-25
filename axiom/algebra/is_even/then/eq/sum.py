from util import *


@apply
def apply(given, self):
    a = given.of(Equal[Expr % 2, 0])
    expr, (i, rgn) = self.of(Sum)
    S[a], b, S[2] = rgn.of(Range)

    return Equal(self, Sum[i:a // 2:(b + 1) // 2](expr._subs(i, 2 * i)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, a, b = Symbol(integer=True)
    f = Symbol(shape=(oo,), real=True)
    Eq << apply(Equal(a % 2, 0), Sum[i:Range(a, b, 2)](f[i]))

    Eq << Eq[1].lhs.this.apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.to.et.split.range)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.absorb)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.st.is_even)

    Eq << algebra.is_even.then.eq.floor.one.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2023-05-30
