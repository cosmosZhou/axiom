from util import *


@apply
def apply(imply, var=None):
    A, B = imply.of(Supset)
    if var is None:
        var = B.element_symbol()

    return All[var:B](Element(var, A))


@prove
def prove(Eq):
    from Axiom import Sets

    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Supset(B, A))

    Eq << Eq[0].reversed

    Eq << Sets.Subset.to.All_In.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-24