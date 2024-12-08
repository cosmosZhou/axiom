from util import *


@apply
def apply(is_positive, z):
    r = is_positive.of(Expr > 0)
    return Equal(Arg(r * z), Arg(z))


@prove
def prove(Eq):
    from Axiom import Algebra

    z = Symbol(complex=True, given=True)
    r = Symbol(real=True)
    Eq << apply(r > 0, z)

    Eq << Algebra.Gt_0.to.Any.Eq.apply(Eq[0])

    Eq <<= Eq[2] & Eq[1]

    Eq << Eq[-1].this.apply(Algebra.Cond.Any.of.Any.And, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.of.And.subs)





if __name__ == '__main__':
    run()
# created on 2018-08-25
# updated on 2023-08-26
