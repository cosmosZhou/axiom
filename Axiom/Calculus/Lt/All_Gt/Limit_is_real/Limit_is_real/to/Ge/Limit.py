from util import *


@apply
def apply(lt, all_gt, limit_is_real_fx, limit_is_real_gx):
    a, b = lt.of(Less)
    (lhs, rhs), (x, domain) = all_gt.of(All[Greater])
    S[a], S[b] = domain.of(Interval)

    (S[lhs], (x, x0)), R = limit_is_real_fx.of(Element[Limit])
    assert R in Reals
    (S[rhs], limit), R = limit_is_real_gx.of(Element[Limit])
    assert R in Reals
    assert limit == (x, x0)

    x0, dir = x0.clear_infinitesimal()
    assert lhs.is_continuous_at(x, domain)
    assert rhs.is_continuous_at(x, domain)
    if dir < 0:
        x0 = b
        assert domain.right_open
    elif dir > 0:
        x0 = a
        assert domain.left_open

    return GreaterEqual(Limit[x:x0 + dir](lhs), Limit[x:x0 + dir](rhs))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra, Sets

    a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    domain = Interval(a, b, right_open=True)
    f, g = Function(real=True, continuous=domain)
    Eq << apply(a < b, All[x:domain](Greater(f(x), g(x))), Element(Limit[x:b - S.Infinitesimal](f(x)), Reals), Element(Limit[x:b - S.Infinitesimal](g(x)), Reals))

    Eq <<= Calculus.All_EqLimit.is_continuous.Interval.apply(f(x), (x, domain)), Calculus.All_EqLimit.is_continuous.Interval.apply(g(x), (x, domain))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.expr.apply(Calculus.Eq_Limit.Eq_Limit.to.Eq_Limit.Sub)

    xi = Eq[-1].variable
    Eq <<= Eq[1].this.expr.apply(Algebra.Gt.to.Gt_0)

    Eq <<= Eq[-1].limits_subs(x, xi)

    Eq <<= Eq[-1] & Eq[-2]

    Eq <<= Eq[-1].this.expr.apply(Algebra.Eq.Gt.to.Gt.subs)

    Eq <<= Algebra.All.to.Imply.apply(Eq[-1])

    epsilon = Symbol(positive=True)
    Eq <<= Eq[-1].subs(xi, b - epsilon)

    Eq <<= Eq[-1].this.lhs.apply(Sets.In.of.In.Neg)

    Eq <<= Eq[-1].this.lhs.apply(Sets.In.of.In.Add, b)

    Eq <<= Eq[-1].this.lhs.apply(Sets.In_Interval.of.And)

    Eq << Algebra.Imply.to.All.apply(Eq[-1])

    Eq << Algebra.Lt.to.Gt_0.apply(Eq[0])

    Eq << Calculus.Gt_0.All_Gt_0.to.Ge_.Limit.Zero.st.Limit.apply(Eq[-1], Eq[-2])

    Eq << Calculus.is_limited.is_limited.to.Eq.Sub.algebraic_limit_theorem.apply(Eq[2], Eq[3])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Sets.Ge.In.to.Ge.Add.apply(Eq[-1], Eq[3])


if __name__ == '__main__':
    run()
# created on 2020-06-26