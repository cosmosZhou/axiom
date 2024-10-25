from util import *


@apply
def apply(lt, gt):
    x, a = lt.of(Less)
    S[x], b = gt.of(Greater)
    return Less(abs(x), Max(abs(a), abs(b)))


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(x < a, x > b)

    Eq << algebra.lt_abs.of.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], -~Eq[-1]

    Eq <<= algebra.ge.then.ge.relax.apply(Eq[-2], abs(a)), -algebra.ge.then.ge.relax.apply(Eq[-1], abs(b))

    Eq <<= algebra.lt.ge.then.gt.trans.apply(Eq[0], Eq[-2]), -algebra.gt.le.then.lt.trans.apply(Eq[1], Eq[-1])

    Eq <<= algebra.then.le.abs.apply(a), algebra.then.le.abs.apply(b, negate=True)

    Eq <<= Eq[-2] & Eq[-4], Eq[-1] & Eq[-3]





if __name__ == '__main__':
    run()
# created on 2019-12-19
# updated on 2023-04-17
