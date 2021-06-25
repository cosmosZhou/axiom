from util import *


def limits_subs(Sum, self, old, new):
    expr, (i, a, b) = self.of(Sum)
    assert old == i
    c = new + i + 1
    #new = c - i - 1
    assert not c._has(i)
    #i = a => new = c - a - 1
    #i = b - 1 => new = c - (b - 1) - 1 = c - b
    return Sum[i:c - b: c - a](expr._subs(old, new))

@apply
def apply(self, old, new):
    return Equal(self, limits_subs(Sum, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    i = Symbol.i(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    f = Function.f(real=True)
    Eq << apply(Sum[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.negate.infinity)

    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.negate)

    Eq << Eq[-1].this.rhs.limits_subs(i, i - c)

    Eq << Eq[-1].this.rhs.find(Contains).apply(sets.contains.add, c)

    Eq << Eq[-1].this.rhs().find(Contains).simplify()


if __name__ == '__main__':
    run()