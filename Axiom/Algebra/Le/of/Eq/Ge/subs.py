from util import *



@apply
def apply(equal, less_than):
    from Axiom.Algebra.Le.of.Eq.Le.subs import ratsimp
    if not less_than.is_GreaterEqual:
        less_than, equal = given

    assert equal.is_Equal
    assert less_than.is_GreaterEqual

    lhs, rhs, k = ratsimp(equal, less_than)
    assert k < 0
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    y, b, x, t = Symbol(real=True)
    k = Symbol(real=True, negative=True)

    Eq << apply(Equal(y, x * k + b), x >= t)

    Eq << Eq[1] * k + b

    Eq << Eq[-1].subs(Eq[0].reversed)

if __name__ == '__main__':
    run()
# created on 2021-09-20
