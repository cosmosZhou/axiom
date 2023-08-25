from util import *


@apply
def apply(ne, eq):
    x = ne.of(Unequal[0])
    lhs, rhs = eq.of(Equal)
    return Equal((x * lhs).expand(), (x * rhs).expand())


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(Unequal(f(x), 0), Equal(g(x) / f(x), h(x) / f(x) + x))

    Eq << Eq[-1] / f(x)

    Eq << ~Eq[-1]

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])

    
    


if __name__ == '__main__':
    run()



# created on 2018-01-24
# updated on 2023-06-06
