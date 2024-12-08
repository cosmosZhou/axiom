from util import *


@apply
def apply(limited_f, limited_g):
    from Axiom.Calculus.is_limited.to.Any.All.limit_definition import of_limited
    fx, (x, x0) = of_limited(limited_f, nonzero=True)
    gx, S[(x, x0)] = of_limited(limited_g, real=True)

    return Equal(Limit[x:x0](fx * gx), limited_f.lhs * limited_g.lhs)


@prove
def prove(Eq):
    from Axiom import Calculus, Sets, Algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0 + S.Infinitesimal](f(x)), Reals - {0}), Element(Limit[x:x0 + S.Infinitesimal](g(x)), Reals))

    ε = Symbol(real=True, positive=True)
    ε_0 = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq.Limit_A_definition = Calculus.is_limited.to.Any.All.limit_definition.symbol_subs.apply(Eq[0], ε_0, δ_0, var='A')

    A = -Eq.Limit_A_definition.expr.expr.lhs.arg.args[0]
    Eq << Eq[0].subs(A.this.definition.reversed)

    Eq.abs_gt_zero = Sets.is_nonzero.to.Gt_0.Abs.apply(Eq[-1])

    Eq.abs_is_positive = Sets.is_nonzero.to.is_positive.Abs.apply(Eq[-1], simplify=None)

    Eq << Sets.is_nonzero.to.is_nonzero.Div.apply(Eq[-1])

    Eq << Sets.is_nonzero.to.is_positive.Abs.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.lhs.apply(Algebra.Abs.eq.Inv, simplify=None)

    Eq.is_positive_real = Sets.In.to.In.Mul.Interval.apply(Eq[-1], ε / 2, simplify=None)

    ε_1 = Symbol(real=True, positive=True)
    δ_1 = Symbol(real=True, positive=True)
    Eq.Limit_B_definition = Calculus.is_limited.to.Any.All.limit_definition.symbol_subs.apply(Eq[1], ε_1, δ_1, var='B')

    B = -Eq.Limit_B_definition.expr.expr.lhs.arg.args[0]
    Eq << Algebra.AbsSubMulS.le.AddMulS_AbsSub.apply(f(x), g(x), A, B)

    δ_2 = Symbol(real=True, positive=True)
    Eq << Calculus.is_limited.to.Any.All.Le.boundedness.apply(Eq[1], delta=δ_2, var='B')

    B = Eq[-1].expr.expr.rhs
    Eq.le = Eq[-1].this.expr.expr.apply(Algebra.Le.Lt.to.Le.subs, Eq[-2])

    assert B > 0
    Eq << Eq.Limit_A_definition.subs(ε_0, ε / B / 2)

    Eq.lt_fx = Eq[-1].this.expr.expr * B

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq.abs_gt_zero, ε / 2, simplify=None)

    Eq << Eq.Limit_B_definition.subs(ε_1, Eq[-1].lhs)

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq.is_positive_real, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Sets.Lt.is_positive.to.Lt.Mul, Eq.abs_is_positive)

    Eq << Algebra.Any_All.Any_All.to.Any.All.And.limits_Intersect.apply(Eq[-1], Eq.lt_fx)

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Lt.to.Lt.Add)

    Eq << Algebra.Any_All.Any_All.to.Any.All.And.limits_Intersect.apply(Eq.le, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Algebra.Lt.Le.to.Lt.trans)

    Eq << Eq[-1].this.expr.apply(Algebra.All.to.Imply)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.of.In.Sub, x0)

    Eq << Eq[-1].this.find(Add[Min]).apply(Algebra.Add.eq.Min)

    delta = Symbol(real=True, positive=True)
    Eq << Algebra.Any.to.Any.subs.apply(Eq[-1], Min(δ_0, δ_1, δ_2), delta)

    Eq << Eq[-1].this.find(Element).apply(Sets.In.of.In.Add, x0)

    Eq << Eq[-1].this.expr.apply(Algebra.Imply.to.All)

    Eq << Calculus.Any_All.to.Eq.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].definition





if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-04-16
# updated on 2021-10-02