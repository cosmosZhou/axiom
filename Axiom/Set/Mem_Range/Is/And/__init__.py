from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    a, b = domain.of(Range)
    assert x.is_integer
    return And(x >= a, x < b)

@prove
def prove(Eq):
    from Axiom import Algebra, Set, Logic

    x, a, b = Symbol(integer=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.And.of.Mem_Range, simplify=False)

    Eq << Eq[-1].this.lhs.apply(Set.Mem.Range.of.Lt.Ge)


if __name__ == '__main__':
    run()
# created on 2020-03-24


from . import split
