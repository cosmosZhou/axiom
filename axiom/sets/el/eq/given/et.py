from util import *


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply
def apply(equal, contains):
    a, A = contains.of(Element)
    _A, union_B_aset = equal.of(Equal)

    if A != _A:
        _A, union_B_aset = union_B_aset, _A

    B, aset = union_B_aset.of(Union)
    if aset != a.set:
        B, aset = aset, B

    return Equal(A - aset, B - aset), Element(a, A)


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Equal(B | a.set, A), Element(a, A))

    Eq << sets.eq.el.imply.eq.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].reversed

    

    
    


if __name__ == '__main__':
    run()

# created on 2021-04-05
# updated on 2023-05-21
