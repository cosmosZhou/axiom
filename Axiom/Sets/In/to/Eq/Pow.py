from util import *


@apply
def apply(el, z):
    r, R = el.of(Element)
    assert R in Reals
    return Equal(Exp(r) ** z, Exp(r * z))


@prove
def prove(Eq):
    from Axiom import Sets

    z = Symbol(complex=True)
    r = Symbol(complex=True)
    f = Function(complex=True)
    Eq << apply(Element(f(r), Reals), z)

    Eq << Sets.In.to.Eq.definition.apply(Eq[0], var='w')

    Eq << Eq[1].subs(Eq[-1].reversed)




if __name__ == '__main__':
    run()
# created on 2023-04-17
