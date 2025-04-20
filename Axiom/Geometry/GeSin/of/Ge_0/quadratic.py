from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr >= 0)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Axiom import Algebra, Geometry, Set, Logic

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[1], cond=x > S.Pi)

    Eq << (x <= 0).this.apply(Geometry.GeSin.of.Le_0.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].this.lhs.apply(Algebra.Le_0.given.Ge)

    Eq << Eq[-1].find(Mul).this.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Pow.eq.Add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq.eq_identity = Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-4].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.given.Gt)

    Eq << Logic.Imp.given.And.Imp.split.apply(Eq[3], cond=x > S.Pi / 2)

    Eq << Logic.Imp.given.And.Imp.invert.apply(Eq[-1], cond=x >= 0)

    Eq << Eq[-1].this.lhs.apply(Set.Mem.Icc.of.Le.Ge)

    Eq << Eq[-1].this.lhs.apply(Geometry.GeSin.of.Mem_Icc.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(Set.Mem.Neg)

    Eq << Eq[-1].this.lhs.apply(Set.Mem_Icc.Is.MemAdd, S.Pi)

    Eq << Eq[-1].this.lhs.apply(Set.Mem_Icc.Is.And)

    Eq << Eq[-1].this.find(And[~GreaterEqual]).apply(Algebra.Ge.given.Gt)




if __name__ == '__main__':
    run()
# created on 2023-10-03
