from util import *


@apply
def apply(given, pivot, left_open=False):
    e, domain = given.of(Element)
    a, b = domain.of(Interval)

    assert domain.conditionally_contains(pivot)
    A = domain.copy(stop=pivot, right_open=not left_open)
    B = domain.copy(start=pivot, left_open=left_open)
    return Or(Element(e, A), Element(e, B))


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol(integer=True, given=True)
    a, b = Symbol(real=True)
    c = Symbol(domain=Interval(a, b))
    Eq << apply(Element(e, Interval(a, b)), pivot=c)

    Eq << sets.ou.of.el.apply(Eq[1])

    Eq << Eq[0].this.rhs.apply(sets.interval.to.union, c)




if __name__ == '__main__':
    run()
# created on 2023-04-18
