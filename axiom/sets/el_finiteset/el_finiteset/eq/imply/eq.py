from util import *


@apply
def apply(x_el_finiteset, y_el_finiteset, eq):
    x, s = x_el_finiteset.of(Element[FiniteSet])
    a, b = s
    y, S[s] = y_el_finiteset.of(Element[FiniteSet])
    fa, fb = eq.of(Equal)
    if fa._has(b):
        fa, fb = fb, fa
    assert not fa._has(b) and fa._subs(a, b) == fb
    return Equal(fa._subs(a, x), fa._subs(a, y))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(
        Element(x, {a, b}),
        Element(y, {a, b}),
        Equal(f(a), f(b)))

    Eq <<= sets.el_finiteset.imply.ou.eq.apply(Eq[0]), sets.el_finiteset.imply.ou.eq.apply(Eq[1])

    Eq <<= Eq[-2].this.args[0].apply(algebra.eq.imply.eq.invoke, f), Eq[-1].this.args[0].apply(algebra.eq.imply.eq.invoke, f)

    Eq <<= Eq[-2].this.args[0].apply(algebra.eq.imply.eq.invoke, f), Eq[-1].this.args[0].apply(algebra.eq.imply.eq.invoke, f)

    Eq <<= Eq[-2].subs(Eq[2]), Eq[-1].subs(Eq[2])

    Eq << algebra.eq.eq.imply.eq.transit.apply(*Eq[-2:])


if __name__ == '__main__':
    run()
# created on 2023-11-10
