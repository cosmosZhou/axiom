from util import *


@apply
def apply(given):
    x_in_A, x_in_B = given.of(Infer)

    x, A = x_in_A.of(Element)
    S[x], B = x_in_B.of(Element)
    assert not x.is_given
    assert x.is_symbol

    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer[n])

    Eq << apply(Infer(Element(x, A), Element(x, B)))

    Eq << Eq[0].this.apply(algebra.infer.to.all, wrt=x)

    Eq << sets.all_el.then.subset.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-04-25
