from util import *


@apply(simplify=False)
def apply(le, el):
    a, b = le.of(GreaterEqual)
    t, s = el.of(Element)
    assert s in Interval(-oo, oo)
    return GreaterEqual(a - t, b - t)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, y, a, b = Symbol(real=True, given=True)
    t = Symbol(hyper_real=True, given=True)
    Eq << apply(x >= y, Element(t, Interval(a, b)))

    Eq << Sets.In.to.In.relax.apply(Eq[1], Reals, simplify=None)

    z = Symbol(real=True)
    Eq << Sets.In.to.Any.Eq.apply(Eq[-1], var=z)

    Eq << Eq[0] - z

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2020-06-23
