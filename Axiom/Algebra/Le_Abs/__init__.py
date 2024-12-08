from util import *


@apply
def apply(x, negate=False):
    if negate:
        x = -x
    return LessEqual(x, abs(x))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << ~Eq[-1]

    Eq << GreaterEqual(abs(x), 0, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(Algebra.Gt.Ge.to.Gt.trans, ret=0, simplify=None)

    Eq << Eq[-1].this.args[0].apply(Algebra.Gt_0.to.Eq.Abs, simplify=None)

    Eq << Eq[-1].this.apply(Algebra.Gt.Eq.to.Gt.trans)



if __name__ == '__main__':
    run()

# created on 2018-06-29
# updated on 2022-01-04

from . import to
from . import of
