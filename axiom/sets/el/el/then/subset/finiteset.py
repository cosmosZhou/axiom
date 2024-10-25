from util import *


@apply
def apply(contains1, contains2):
    x, A = contains1.of(Element)
    y, S[A] = contains2.of(Element)

    return Subset({x, y}, A)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x, y = Symbol(integer=True)
    S = Symbol(etype=dtype.integer)

    Eq << apply(Element(x, S), Element(y, S))

    Eq << sets.subset.of.all_el.apply(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.all.to.et.doit.setlimit)

    Eq << algebra.et.of.et.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-03-29
