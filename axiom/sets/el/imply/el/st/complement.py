from util import *


@apply
def apply(given):
    e, domain = given.of(Element)
    S, s = domain.of(Complement)
    return Element(e, S)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(integer=True)
    U, s = Symbol(etype=dtype.integer)

    Eq << apply(Element(x, U - s))

    Eq << Subset(Eq[0].rhs, Eq[1].rhs, plausible=True)

    Eq << sets.el.subset.imply.el.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-01-12
# updated on 2018-01-12
