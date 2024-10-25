from util import *


@apply
def apply(le, sgm):
    b, a = le.of(LessEqual)
    expr, (k, S[a], S[b]) = sgm.of(Sum)
    return Equal(sgm, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(integer=True, given=True)
    n = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(b <= a, Sum[n:a:b](f(n)))

    Eq << algebra.ge.then.sum_is_zero.apply(Eq[0].reversed, Eq[1].lhs)






if __name__ == '__main__':
    run()
# created on 2019-11-18
