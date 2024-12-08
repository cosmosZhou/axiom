from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    a, b = domain.of(Interval)
    assert domain.right_open
    if domain.left_open:
        assert a.is_infinite
    else:
        if not a.is_integer:
            a = Floor(a)

    if not b.is_integer:
        b = Ceiling(b)

    return Element(Floor(x), Range(a, b))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << Sets.In.to.In.Neg.apply(Eq[0])

    Eq << Sets.In_Interval.to.In_Range.Ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Ceiling.eq.Neg.Floor)

    Eq << Sets.In.to.In.Neg.apply(Eq[-1])

    Eq << Eq[-1].this.find(-~Ceiling).apply(Algebra.Ceiling.eq.Neg.Floor)

    Eq << Eq[-1].this.find(-~Floor).apply(Algebra.Floor.eq.Neg.Ceiling)




if __name__ == '__main__':
    run()
# created on 2021-03-05
# updated on 2023-04-17
