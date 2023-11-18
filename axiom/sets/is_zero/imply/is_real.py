from util import *


@apply
def apply(given):
    x = given.of(Equal[0])
    return Element(x, Reals)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(super_complex=True)
    e = Symbol(real=True)
    Eq << apply(Equal(x, 0))

    Eq << sets.eq.imply.is_real.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-04-18
