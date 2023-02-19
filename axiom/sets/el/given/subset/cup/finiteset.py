from util import *


@apply
def apply(el):
    e, S = el.of(Element)

    [n] = e.shape
    i = el.generate_var(integer=True)
    
    return Subset(e.cup_finiteset(i), S.space)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(integer=True, shape=(oo,))
    S = Symbol(etype=dtype.integer)
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Element(x[:n], CartesianSpace(S, n)))

    Eq << sets.subset_cup.imply.all_subset.apply(Eq[1])

    Eq << sets.all_el.imply.el.cartesianSpace.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2022-09-20
