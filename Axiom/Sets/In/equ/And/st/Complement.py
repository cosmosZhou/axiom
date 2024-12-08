from util import *


@apply
def apply(given):
    x, complement = given.of(Element)

    B, A = complement.of(Complement)
    return And(Element(x, B), NotElement(x, A))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    Eq << apply(Element(x, B - A))

    Eq.suffice, Eq.necessary = Algebra.Iff.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.of.And.Imply.apply(Eq.suffice)

    Eq << Eq[-2].this.lhs.apply(Sets.In.to.In.st.Complement)

    Eq << Eq[-1].this.lhs.apply(Sets.In.to.NotIn.st.Complement)

    Eq << Eq.necessary.this.lhs.simplify()


if __name__ == '__main__':
    run()

# created on 2021-01-25
