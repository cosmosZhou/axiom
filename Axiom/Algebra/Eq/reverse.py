from util import *


@apply
def apply(eq):
    a, b = eq.of(Equal)
    return Equal(b, a)


@prove
def prove(Eq):
    from Axiom import Algebra

    b, a = Symbol(real=True, given=True)
    Eq << apply(Equal(a, b))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-04-19
