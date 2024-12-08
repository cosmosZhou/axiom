from util import *


@apply
def apply(given, right_open=True):
    x, (a, b, d) = given.of(Element[Range])
    if right_open:
        return x >= a, x < b, Equal(x % d, a % d)
    else:
        return x >= a, x <= b - 1, Equal(x % d, a % d)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(integer=True, given=True)
    a, b = Symbol(integer=True, given=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b, d)), False)

    Eq << Sets.In_Range.equ.And.split.st.dilated.apply(Eq[0])

    Eq << Algebra.Cond.Iff.to.Cond.trans.apply(Eq[0], Eq[-1])

    Eq << Algebra.And.to.And.apply(Eq[-1], None)

    Eq << Algebra.Lt.to.Le.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-01-01
