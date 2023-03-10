from util import *



@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)

    assert lhs.is_real
    assert rhs.is_real
    assert rhs >= 0

    return GreaterEqual(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    y = Symbol(real=True, nonnegative=True)

    Eq << apply(GreaterEqual(x, y))

    Eq << algebra.ge.ge.imply.ge.mul.apply(Eq[0], Eq[0])



if __name__ == '__main__':
    run()

# created on 2019-06-01
