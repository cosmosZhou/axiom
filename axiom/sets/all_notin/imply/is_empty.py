from util import *


@apply
def apply(given):
    (e, A), (S[e], B) = given.of(All[NotElement])
    return Equal(A & B, e.emptySet)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)

    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(All[x: A](NotElement(x, B)))

    Eq << algebra.all.imply.ou.apply(Eq[0], simplify=False)

    Eq << ~Eq[-1]

    Eq << ~Eq[1]


if __name__ == '__main__':
    run()

# created on 2018-03-05
