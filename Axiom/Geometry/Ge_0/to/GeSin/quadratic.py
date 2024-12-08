from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr >= 0)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Axiom import Algebra, Geometry, Sets

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=x > S.Pi)

    Eq << (x <= 0).this.apply(Geometry.Le_0.to.GeSin.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].this.lhs.apply(Algebra.Le_0.of.Ge)

    Eq << Eq[-1].find(Mul).this.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Pow.eq.Add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq.eq_identity = Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-4].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Gt)

    Eq << Algebra.Imply.of.And.Imply.split.apply(Eq[3], cond=x > S.Pi / 2)

    Eq << Algebra.Imply.of.And.Imply.invert.apply(Eq[-1], cond=x >= 0)

    Eq << Eq[-1].this.lhs.apply(Sets.Le.Ge.to.In.Interval)

    Eq << Eq[-1].this.lhs.apply(Geometry.In_Interval.to.GeSin.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(Sets.In.Neg)

    Eq << Eq[-1].this.lhs.apply(Sets.In.Add, S.Pi)

    Eq << Eq[-1].this.lhs.apply(Sets.In_Interval.equ.And)

    Eq << Eq[-1].this.find(And[~GreaterEqual]).apply(Algebra.Ge.of.Gt)




if __name__ == '__main__':
    run()
# created on 2023-10-03
