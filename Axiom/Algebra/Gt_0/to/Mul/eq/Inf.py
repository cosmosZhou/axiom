from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Inf)
    return Equal(self * a, Inf(fx * a, *limits))


@prove
def prove(Eq):
    from Axiom import Algebra

    m, M, x, a, b, c = Symbol(real=True, given=True)
    f = Function(real=True)
    Eq << apply(a > 0, Inf[x:Interval(m, M, left_open=True, right_open=True)](f(x)))

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[0])

    y = Symbol(Eq[1].lhs.args[1])
    Eq << y.this.definition

    Eq <<= Algebra.Eq.to.And.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed).reversed

    Eq <<= Algebra.LeInf.to.All.Any.Lt.apply(Eq[-3]), Algebra.GeInf.to.All.Ge.apply(Eq[-2]), Algebra.Eq.of.And.squeeze.apply(Eq[-1])

    y_ = Eq[-4].variable
    Eq <<= Algebra.All.to.Imply.apply(Eq[-4]), Algebra.GeInf.of.All.Ge.apply(Eq[-1]), Algebra.LeInf.of.All_Any_Lt.apply(Eq[-2])

    Eq <<= Eq[-3].subs(y_, Eq[2].lhs * y_), Eq[-2].this.expr.apply(Algebra.Ge.of.And.scale.positive, a, div=True), Algebra.All.of.Imply.apply(Eq[-1])

    Eq << Algebra.And.of.And.apply(Eq[-2])

    Eq << Eq[-3].this.rhs.apply(Algebra.Cond.Any.to.Any.And, Eq[0], simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.Gt_0.Lt.to.Lt.Mul)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.of.And.scale.positive, a)

    Eq << Algebra.Cond.Cond.to.Cond.subs.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-17
