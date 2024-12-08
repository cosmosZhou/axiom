from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    assert x.is_integer and a.is_integer
    return GreaterEqual(a, x + 1).simplify()


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x < a)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Lt.to.Le.strengthen), Eq[-1].this.rhs.apply(Algebra.Lt.of.Le.strengthen)

    Eq <<= Eq[-2].this.lhs.reversed, Eq[-1].this.rhs.reversed

    Eq <<= Eq[-2].this.lhs + 1, Eq[-1].this.rhs + 1





if __name__ == '__main__':
    run()
# created on 2021-12-17
