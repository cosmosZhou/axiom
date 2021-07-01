from util import *


@apply
def apply(*given):
    from axiom.algebra.lt.eq.imply.lt.transit import swap
    return Greater(*swap(Greater, *given))


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    #Eq << apply(b > x, Equal(x, a))
    Eq << apply(b > x, Equal(a, x))

    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].this.apply(algebra.gt.simplify.common_terms)


if __name__ == '__main__':
    run()