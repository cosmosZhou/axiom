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
    from Axiom import Sets, Algebra

    a, b, x, y = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(
        Element(x, {a, b}),
        Element(y, {a, b}),
        Equal(f(a), f(b)))

    Eq <<= Sets.In_FiniteSet.to.Or.Eq.apply(Eq[0]), Sets.In_FiniteSet.to.Or.Eq.apply(Eq[1])

    Eq <<= Eq[-2].this.args[0].apply(Algebra.Eq.to.Eq.invoke, f), Eq[-1].this.args[0].apply(Algebra.Eq.to.Eq.invoke, f)

    Eq <<= Eq[-2].this.args[0].apply(Algebra.Eq.to.Eq.invoke, f), Eq[-1].this.args[0].apply(Algebra.Eq.to.Eq.invoke, f)

    Eq <<= Eq[-2].subs(Eq[2]), Eq[-1].subs(Eq[2])

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(*Eq[-2:])


if __name__ == '__main__':
    run()
# created on 2023-11-10
