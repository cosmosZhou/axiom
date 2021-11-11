from util import *


@apply
def apply(f0, f1, suffice, n=None, start=0):
    start = sympify(start)
    f0.of(Equal)
    f1.of(Equal)
    fn, fn2 = suffice.of(Infer)
    assert fn._subs(n, n + 2) == fn2

    assert fn._subs(n, start) == f0
    assert fn._subs(n, start + 1) == f1
    assert n.domain.min() == start

    return fn


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    f, g = Symbol(integer=True, shape=(oo,))
    Eq << apply(Equal(f[1], g[1]), Equal(f[2], g[2]), Infer(Equal(f[n], g[n]), Equal(f[n + 2], g[n + 2])), n=n, start=1)

    m = Symbol(integer=True, nonnegative=True, given=False)
    h = Symbol(Lamda[m](f[2 * m + 1] - g[2 * m + 1]))
    Eq << h[0].this.definition

    Eq.is_zero = Eq[-1].this.rhs.subs(Eq[0])

    Eq.suffice = Infer(Equal(h[m], 0), Equal(h[m + 1], 0), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[2].subs(n, 2 * m + 1)

    Eq << algebra.is_zero.infer.imply.is_zero.induct.apply(Eq.is_zero, Eq.suffice, n=m)

    Eq << Eq[-1].this.lhs.definition

    Eq.odd = Eq[-1].reversed

    h = Symbol("h'", Lamda[m](f[2 * m + 2] - g[2 * m + 2]))
    Eq << h[0].this.definition

    Eq.is_zero_even = Eq[-1].this.rhs.subs(Eq[1])

    Eq.suffice_even = Infer(Equal(h[m], 0), Equal(h[m + 1], 0), plausible=True)

    Eq << Eq.suffice_even.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[2].subs(n, 2 * m + 2)

    Eq << algebra.is_zero.infer.imply.is_zero.induct.apply(Eq.is_zero_even, Eq.suffice_even, n=m)

    Eq << Eq[-1].this.lhs.definition

    Eq.even = Eq[-1].reversed

    Eq << algebra.eq.imply.all_eq.limit_is_odd.apply(Eq.odd, m)

    Eq << algebra.eq.imply.all_eq.limit_is_even.apply(Eq.even, m)

    Eq << Eq[-1].this.apply(algebra.all.limits.subs.offset, -2)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].subs(m, n)


if __name__ == '__main__':
    run()

# created on 2019-03-28
# updated on 2019-03-28
