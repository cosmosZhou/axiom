from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Sup, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= Algebra.Eq.to.And.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= Algebra.LeSup.to.All.Le.apply(Eq[-3]), Algebra.GeSup.to.All.Any.Gt.apply(Eq[-2]), Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeSup.of.All.Le.apply(Eq[-2]), Algebra.GeSup.of.All_Any_Gt.apply(Eq[-1])

    Eq << Algebra.All.of.All.limits.subs.offset.apply(Eq[-2], -t)
    Eq << Eq[-1].this.expr.apply(Algebra.Any.of.Any.limits.subs.offset, -t)




if __name__ == '__main__':
    run()
# created on 2019-08-29
