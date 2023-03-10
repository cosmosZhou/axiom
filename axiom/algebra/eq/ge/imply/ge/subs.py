from util import *





@apply
def apply(equal, less_than):
    from axiom.algebra.eq.le.imply.le.subs import ratsimp
    assert equal.is_Equal
    assert less_than.is_GreaterEqual

    lhs, rhs, k = ratsimp(equal, less_than)
    assert k > 0
    return GreaterEqual(lhs, rhs)


@prove
def prove(Eq):
    y, b, x, t = Symbol(real=True)
    k = Symbol(real=True, positive=True)
    Eq << apply(Equal(y, x * k + b), x >= t)

    Eq << Eq[1] * k + b

    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2021-03-19
