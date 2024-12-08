from util import *


@apply
def apply(is_real, eq):
    a, C = is_real.of(Element)
    assert C in Reals
    b, c = eq.of(Equal)
    return Equal(a + b, a + c)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y, z = Symbol(super_real=True)
    Eq << apply(Element(x, Reals), Equal(y - x, z))

    Eq << Sets.In.to.Eq.definition.apply(Eq[0], var='a').reversed

    Eq <<= Eq[1].subs(Eq[-1]), Eq[2].subs(Eq[-1])

    Eq << Eq[-2] + Eq[3].rhs


if __name__ == '__main__':
    run()
# created on 2023-06-29
