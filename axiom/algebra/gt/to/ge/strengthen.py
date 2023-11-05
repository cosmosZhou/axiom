from util import *


@apply
def apply(gt, step=1):
    lhs, rhs = gt.of(Greater)
    assert rhs.is_integer and lhs.is_integer
    if step > 0:
        rhs += 1
    else:
        lhs -= 1

    return GreaterEqual(lhs, rhs).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True)
    Eq << apply(x > a)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt.imply.ge.strengthen), Eq[-1].this.rhs.apply(algebra.gt.given.ge.strengthen)

    Eq <<= Eq[-2].this.lhs.reversed, Eq[-1].this.rhs.reversed

    Eq <<= Eq[-2].this.lhs + 1, Eq[-1].this.rhs + 1

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-02
# updated on 2023-11-05
