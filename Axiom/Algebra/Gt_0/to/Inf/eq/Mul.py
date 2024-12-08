from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Inf)
    return Equal(Inf(fx * a, *limits), a * self)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, x, m, M = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a > 0, Inf[x:m:M](f(x)))

    Eq.reciprocal = Algebra.Gt_0.to.Gt_0.Div.apply(Eq[0])

    y = Symbol(Eq[1].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq << Algebra.Eq.to.And.squeeze.apply(Eq[-1])

    z = Symbol(real=True)
    Eq <<= Algebra.LeInf.to.All.Any.Lt.apply(Eq[-2], z), Algebra.GeInf.to.All.Ge.apply(Eq[-1])

    Eq <<= Algebra.All.to.Imply.apply(Eq[-2]), Algebra.All.to.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].subs(z, z * Eq.reciprocal.lhs), Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq[0], Eq[-1])

    Eq <<= Algebra.Imply.to.Imply.And.both_sided.apply(Eq[-2], cond=Eq[0]), Eq[-1].this.rhs.apply(Algebra.Gt_0.Ge.to.Ge.Mul)

    Eq << Eq[-2].this.rhs.apply(Algebra.Cond.Any.to.Any.And, simplify=None)

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Gt_0.Lt.to.Lt.Mul)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Gt.of.And.scale.positive, a)

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(Eq[2])

    Eq << Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    Eq <<= Algebra.LeInf.of.All_Any_Lt.apply(Eq[-2], z), Algebra.GeInf.of.All.Ge.apply(Eq[-1])

    Eq <<= Algebra.All.of.Imply.apply(Eq[-2]), Algebra.All.of.Imply.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-13
