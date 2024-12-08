from util import *


@apply
def apply(imply, wrt=None):
    B, A = imply.of(Subset)
    if wrt is None:
        wrt = imply.generate_var(**B.etype.dict)
    elif isinstance(wrt, str):
        wrt = imply.generate_var(**B.etype.dict, var=wrt)

    return All[wrt:B](Element(wrt, A))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex[n], given=True)
    Eq << apply(Subset(B, A))

    Eq << Sets.Subset.of.Eq_EmptySet.Complement.apply(Eq[0])

    Eq << ~Eq[-1]

    Eq << Sets.Ne_EmptySet.to.Any_In.st.Complement.apply(Eq[-1], simplify=False, wrt=Eq[1].variable)

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-03-27
