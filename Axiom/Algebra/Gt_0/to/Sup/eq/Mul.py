from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Sup)
    return Equal(Sup(fx * a, *limits), a * self)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a > 0, Sup[x:m:M](f(x)))

    Eq.reciprocal = Algebra.Gt_0.to.Gt_0.Div.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << Algebra.Eq.to.And.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= Algebra.LeSup.to.All.Le.apply(Eq[-2]), Algebra.GeSup.to.All.Any.Gt.apply(Eq[-1], z)

    Eq <<= Algebra.All.to.Imply.apply(Eq[-2]), Algebra.All.to.Imply.apply(Eq[-1])

    Eq <<= Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq[0], Eq[-2]), Eq[-1].subs(z, z * Eq.reciprocal.lhs)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Gt_0.Le.to.Le.Mul), Algebra.Imply.to.Imply.And.both_sided.apply(Eq[-1], cond=Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Gt_0.Gt.to.Gt.Mul)

    Eq << Eq[-1].this.find(Less).apply(Algebra.Lt.of.And.scale.positive, a)

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeSup.of.All.Le.apply(Eq[-2]), Algebra.GeSup.of.All_Any_Gt.apply(Eq[-1], z)

    Eq <<= Algebra.All.of.Imply.apply(Eq[-2]), Algebra.All.of.Imply.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2019-08-21
# updated on 2023-05-14
