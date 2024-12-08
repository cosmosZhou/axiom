from util import *



@apply
def apply(given):
    A, B = given.of(Equal[Intersection, EmptySet])
    if A.is_FiniteSet:
        if len(A) != 1:
            swap = True
        else:
            swap = False
    else:
        swap = True

    if swap:
        A, B = B, A

    a = A.of(FiniteSet)

    return NotElement(a, B)


@prove
def prove(Eq):
    from Axiom import Sets

    a = Symbol(integer=True, given=True)
    B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(a.set & B, a.emptySet))

    Eq << Sets.NotIn.to.Eq.Complement.apply(Eq[1]).reversed

    Eq << Sets.Eq.to.Eq.Intersect.apply(Eq[-1], {a})






if __name__ == '__main__':
    run()
# created on 2019-02-02
