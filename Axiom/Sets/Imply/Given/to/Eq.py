from util import *


@apply
def apply(sufficient_A, necessary_B):
    x_in_A, x_in_B = sufficient_A.of(Imply)

    S[x_in_A], S[x_in_B] = necessary_B.of(Given)

    x, A = x_in_A.of(Element)
    S[x], B = x_in_B.of(Element)
    assert not x.is_given
    assert x.is_symbol

    return Equal(A, B)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer[n])

    Eq << apply(Imply(Element(x, A), Element(x, B)), Given(Element(x, A), Element(x, B)))

    Eq << Eq[0].this.apply(Algebra.Imply.equ.All, wrt=x)

    Eq << Algebra.Given.to.All.apply(Eq[1], wrt=x)

    Eq << Sets.All_In.All_In.to.Eq.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-09-19
