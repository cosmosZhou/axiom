from util import *


@apply
def apply(imply):
    (x, S), *limits = imply.of(Any[Element])
    return Element(x, Cup(S, *limits))


@prove
def prove(Eq):
    from Axiom import Set

    n = Symbol(positive=True, integer=True)
    x, k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer)
    Eq << apply(Any[k:n](Element(x, A[k])))

    Eq << Set.Mem_Cup.given.Any_Mem.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-10-23
