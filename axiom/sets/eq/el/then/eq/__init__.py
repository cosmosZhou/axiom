from util import *


@apply
def apply(equal, contains):
    a, A = contains.of(Element)

    complement_A_a, complement_B_a = equal.of(Equal)
    _A, _a = complement_A_a.of(Complement)
    S[a] = _a.of(FiniteSet)

    B, _a = complement_B_a.of(Complement)
    S[a] = _a.of(FiniteSet)

    if A != _A:
        S[A], B = B, _A

    return Equal(A, B | a.set)


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(etype=dtype.integer, given=True)
    a = Symbol(integer=True, given=True)
    Eq << apply(Equal(A - a.set, B - a.set), Element(a, A))

    Eq << sets.eq.then.eq.union.apply(Eq[0], a.set)

    Eq << sets.el.then.eq.union.apply(Eq[1])

    Eq << Eq[-2].this.lhs.subs(Eq[-1])


if __name__ == '__main__':
    run()


from . import finiteset
# created on 2021-03-27
