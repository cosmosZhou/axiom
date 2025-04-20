from util import *


@apply
def apply(is_positive, self):
    a = is_positive.of(Expr > 0)
    fx, *limits = self.of(Inf)
    return Equal(self * a, Inf(fx * a, *limits))


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    m, M, x, a, b, c = Symbol(real=True, given=True)
    f = Function(real=True)
    Eq << apply(a > 0, Inf[x:Interval(m, M, left_open=True, right_open=True)](f(x)))

    Eq << Algebra.Gt_0.Div.of.Gt_0.apply(Eq[0])

    y = Symbol(Eq[1].lhs.args[1])
    Eq << y.this.definition

    Eq <<= Algebra.And.of.Eq.squeeze.apply(Eq[-1].reversed), Eq[1].subs(Eq[-1].reversed).reversed

    Eq <<= Algebra.All.Any.Lt.of.LeInf.apply(Eq[-3]), Algebra.All.Ge.of.GeInf.apply(Eq[-2]), Algebra.Eq.given.And.squeeze.apply(Eq[-1])

    y_ = Eq[-4].variable
    Eq <<= Logic.Imp.of.All.apply(Eq[-4]), Algebra.GeInf.given.All.Ge.apply(Eq[-1]), Algebra.LeInf.given.All_Any_Lt.apply(Eq[-2])

    Eq <<= Eq[-3].subs(y_, Eq[2].lhs * y_), Eq[-2].this.expr.apply(Algebra.Ge.given.And.scale.positive, a, div=True), Logic.All.given.Imp.apply(Eq[-1])

    Eq << Algebra.And.given.And.apply(Eq[-2])

    Eq << Eq[-3].this.rhs.apply(Algebra.Any.And.of.Cond.Any, Eq[0], simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.LtMul.of.Gt_0.Lt)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.given.And.scale.positive, a)

    Eq << Algebra.Cond.of.Cond.Cond.subs.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-17
