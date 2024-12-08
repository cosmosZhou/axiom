from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert domain.left_open
    if domain.right_open:
        assert b.is_infinite
    else:
        if not b.is_integer:
            b = Ceiling(b)

    if not a.is_integer:
        a = Floor(a)
    return Element(Ceiling(x), Range(a + 1, b + 1))


@prove
def prove(Eq):
    from Axiom import Sets

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)))

    Eq << Sets.In.to.In.relax.Interval.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Sets.Interval.eq.Cup.left_open)

    Eq << Sets.In_Cup.to.Any_In.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Sets.In.to.Eq.Ceiling)

    Eq << Eq[-1].this.expr.apply(Sets.Eq.to.In.FiniteSet)

    Eq << Sets.Any_In.to.In.Cup.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Sets.Cup.limits.subs.offset, -1)




if __name__ == '__main__':
    run()
# created on 2018-10-24
# updated on 2023-04-17
