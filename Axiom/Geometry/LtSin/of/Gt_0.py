from util import *


@apply
def apply(gt_zero):
    x = gt_zero.of(Expr > 0)
    return sin(x) < x

@prove
def prove(Eq):
    from Axiom import Geometry

    x = Symbol(real=True)
    Eq << apply(x > 0)

    Eq << Geometry.LeSin.of.Gt_0.apply(Eq[0])

    Eq << Geometry.NeSin.of.Gt_0.apply(Eq[0])

    Eq <<= Eq[-1] & Eq[-2]




if __name__ == '__main__':
    run()
# created on 2023-10-03
