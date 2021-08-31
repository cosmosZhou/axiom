from util import *


from axiom.algebra.eq.le.imply.le.subs import ratsimp

@apply
def apply(equal, less_than):
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
