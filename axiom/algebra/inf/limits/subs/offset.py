from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Inf, self, index, offset), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b, t = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:a:b](f(x)), t)

    y = Symbol(Eq[-1].lhs)
    Eq << y.this.definition

    Eq << Eq[-1].reversed

    Eq <<= Algebra.Eq.to.And.squeeze.apply(Eq[-1]), Eq[0].reversed.subs(Eq[-1])

    Eq <<= Algebra.LeInf.to.All.Any.Lt.apply(Eq[-3]), Algebra.GeInf.to.All.Ge.apply(Eq[-2]), Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeInf.of.All_Any_Lt.apply(Eq[-2]), Algebra.GeInf.of.All.Ge.apply(Eq[-1])

    Eq << Eq[-2].this.expr.apply(Algebra.Any.of.Any.limits.subs.offset, -t)
    Eq << Algebra.All.of.All.limits.subs.offset.apply(Eq[-1], -t)



if __name__ == '__main__':
    run()
# created on 2019-10-03
