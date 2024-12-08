from util import *


@apply
def apply(el_c, el_x, start=True, stop=False):
    c, s0 = el_c.of(Element)
    x, s = el_x.of(Element)

    assert s0 in s

    assert s.is_Range or s.is_Interval
    if stop:
        s = s.copy(stop=c)
    elif start:
        s = s.copy(start=c)
    return el_c, Element(x, s)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, c, x = Symbol(real=True)
    Eq << apply(Element(c, Interval.open(a, b)), Element(x, Interval(a, b)))

    Eq << Sets.In_Interval.to.And.apply(Eq[-1])

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq << Algebra.Ge.Gt.to.Gt.trans.apply(Eq[-4], Eq[-2])

    Eq << Algebra.Gt.to.Ge.relax.apply(Eq[-1])

    Eq << Sets.In_Interval.of.And.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2023-10-15
