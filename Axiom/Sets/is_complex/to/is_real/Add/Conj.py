from util import *


@apply
def apply(is_complex):
    x, C = is_complex.of(Element)
    assert C in S.Complexes
    return Element(x + ~x, Reals)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(super_complex=True)
    Eq << apply(Element(x, S.Complexes))

    Eq << Sets.In.to.Eq.definition.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Expr.eq.Add.complex)

    Eq << Eq[1].subs(Eq[-1].reversed)






if __name__ == '__main__':
    run()
# created on 2023-05-25
