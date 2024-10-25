from util import *


@apply
def apply(given):
    e, domain = given.of(Element)
    A, B = domain.of(Complement)

    return Element(e, A)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A - B))

    Eq << sets.el_complement.then.et.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-04-25
