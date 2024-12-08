from util import *


@apply
def apply(le, ge, contains):
    _a, a = le.of(LessEqual)
    _b, b = ge.of(GreaterEqual)
    x, domain = contains.of(Element)
    S[a], S[b] = domain.of(Interval)

    return Element(x, Interval(_a, _b, **domain.kwargs))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, a_quote, b_quote, x = Symbol(real=True, given=True)
    Eq << apply(a_quote <= a, b_quote >= b, Element(x, Interval(a, b, right_open=True)))

    Eq << Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Sets.In_Interval.to.And.apply(Eq[2])

    Eq << Algebra.Ge.Le.to.Ge.trans.apply(Eq[-2], Eq[0])
    Eq << Algebra.Lt.Ge.to.Lt.trans.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-11-05
