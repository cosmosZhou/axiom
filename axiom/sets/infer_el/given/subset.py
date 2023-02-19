from util import *


@apply
def apply(given):
    x_in_A, x_in_B = given.of(Infer)

    x, A = x_in_A.of(Element)
    S[x], B = x_in_B.of(Element)
    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    A, B = Symbol(etype=dtype.integer * n)
    Eq << apply(Infer(Element(x, A), Element(x, B)))

    Eq << sets.subset.imply.infer.el.apply(Eq[1], x)

    

    

    


if __name__ == '__main__':
    run()
# created on 2022-09-20
