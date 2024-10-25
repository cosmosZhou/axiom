from util import *


@apply
def apply(lt, n):
    x, a = lt.of(GreaterEqual)
    assert a >= 0
    assert n >= 0 # n could be zero!
    return x ** n >= a ** n


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(real=True)
    a = Symbol(real=True, nonnegative=True)
    Eq << apply(x >= a, n)

    Eq << Eq[1].subs(n, 1)

    Eq << Eq[1].subs(n, n + 1)

    Eq << algebra.ge.ge.then.ge.mul.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.pow.add.exponent)

    Eq << Infer(Eq[1], Eq[2], plausible=True)

    Eq << algebra.cond.infer.then.cond.induct.apply(Eq[0], Eq[-1], n, 1)




if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-10-04
