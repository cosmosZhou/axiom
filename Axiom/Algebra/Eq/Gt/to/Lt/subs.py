from util import *


@apply
def apply(equal, less_than):
    from Axiom.Algebra.Eq.Le.to.Le.subs import ratsimp
    if not less_than.is_Greater:
        less_than, equal = given
    assert equal.is_Equal
    assert less_than.is_Greater

    lhs, rhs, k = ratsimp(equal, less_than)
    assert k < 0
    return Less(lhs, rhs)


@prove
def prove(Eq):
    y, b, x, t = Symbol(real=True)
    k = Symbol(real=True, negative=True)



    Eq << apply(Equal(y, x * k + b), x > t)

    Eq << Eq[1] * k + b

    Eq << Eq[-1].subs(Eq[0].reversed)

if __name__ == '__main__':
    run()
# created on 2020-07-16
