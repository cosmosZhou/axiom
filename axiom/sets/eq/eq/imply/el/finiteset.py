from util import *



@apply
def apply(equality_A, equality_B):
    x, a = equality_A.of(Equal)
    S[x], b = equality_B.of(Equal)

    return Element(x, a.set & b.set)


@prove
def prove(Eq):
    from axiom import algebra
    x, a, b = Symbol(integer=True)

    Eq << apply(Equal(x, a), Equal(x, b))

    Eq << Eq[-1].subs(Eq[1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-12-23
