from util import *


@apply
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    assert x in Interval(-1, 1)
    return Equal(asin(sqrt(1 - x ** 2)) - asin(x), S.Pi / 2)


@prove
def prove(Eq):
    from Axiom import Geometry, Algebra, Set, Logic

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x <= 0)

    Eq << Geometry.Cos.eq.Sub.apply(cos(Eq[1].lhs))

    Eq << Algebra.EqAbs.of.Le_0.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Geometry.Cos.Neg)
    Eq << Geometry.Any.Eq.of.Cos.eq.Zero.apply(Eq[-1])

    Eq << -Eq[-1].this.expr

    Eq << Eq[-1].this.apply(Algebra.Any.limits.Neg.Infty)

    Eq << Algebra.Any.of.Any.limits.subs.offset.apply(Eq[-1], 1)

    Eq.any_eq = Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << GreaterEqual(x, -1, plausible=True)

    Eq << Set.Mem.Icc.of.Ge.Le.apply(Eq[-1], Eq[0])

    Eq <<= Geometry.Mem.Arcsin.of.Mem.apply(Eq[-1]), Set.Mem.Sqrt.Max.of.Mem.apply(Eq[-1])

    Eq <<= Set.Neg.In.IccNegS.of.Mem_Icc.apply(Eq[-2]), Geometry.Mem.Arcsin.of.Mem.apply(Eq[-1])

    Eq << Set.Mem.Add.Icc.of.Mem.Mem.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Any.And.of.Cond.Any.apply(Eq[-1], Eq.any_eq, simplify=None)

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subs, ret=0)

    Eq << Eq[-1].this.find(Element).apply(Set.MemSub.of.Mem_Icc, S.Pi / 2)

    Eq << Eq[-1].this.find(Element).apply(Set.MemDiv.of.Mem_Icc, S.Pi)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)



if __name__ == '__main__':
    run()
# created on 2018-07-13
# updated on 2023-05-20
