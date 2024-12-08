from util import *


@apply
def apply(is_limited):
    from Axiom.Calculus.is_limited.to.Any.All.limit_definition import of_limited
    fx, (x, x0) = of_limited(is_limited, positive=True)
    return Equal(Limit[x:x0](log(fx)), log(Limit[x:x0](fx)))


@prove(proved=False)
def prove(Eq):
    from Axiom import Calculus, Sets, Algebra

    x, x0 = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Element(Limit[x:x0](f(x)), Interval.open(0, oo)))

    epsilon0, delta0, delta, epsilon = Symbol(positive=True)
    Eq << Calculus.is_limited.to.Any.All.limit_definition.symbol_subs.apply(Eq[0], epsilon0, delta0, var='A')

    A = Eq[-1].expr.expr.find(Add[-~Symbol])
    Eq.is_limited = A.this.definition.reversed

    Eq << Eq[0].subs(Eq.is_limited)

    Eq.A_is_positive = Sets.is_positive.to.Gt_0.apply(Eq[-1])

    Eq << Algebra.Gt_0.Eq.to.Eq.Log.apply(Eq.A_is_positive, Eq.is_limited)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << Sets.In.to.Ne_0.apply(Eq[0])

    Eq << Eq[-2].this.apply(Calculus.Eq.equ.Any_All.limit_definition, delta=delta, epsilon=epsilon)

    Eq << Eq[-1].this.expr.expr.lhs.arg.apply(Algebra.Add.eq.Log)

    Eq << Eq[2].this.expr.expr.apply(Algebra.Lt.to.And.split.Abs)

    Eq << Eq[-1].this.expr.expr.args[0].apply(Algebra.Lt.transport, lhs=0)

    Eq << Eq[-1].this.expr.expr.args[0].apply(Algebra.Gt.transport, lhs=0)

    Eq << Eq[-1].this.expr.expr.apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Algebra.Cond.Any_All.to.Any.All.And.apply(Eq.A_is_positive, Eq[-1])

    Eq << Eq[-1].this.expr.expr.apply(Sets.Gt_0.In.to.In.Div)

    Eq << Eq[-1].this.expr.expr.rhs.args[0].apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.expr.expr.rhs.args[1].apply(Algebra.Mul.eq.Add)

    epsilon1 = Symbol(domain=Interval(0, 1, left_open=True, right_open=True))
    Eq << Algebra.Cond.to.Or.subs.apply(Eq[-1], epsilon0, epsilon1 * A)

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq.A_is_positive * epsilon1, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-19
