from util import *


@apply
def apply(eq_conditioned, dist):
    (x, i), (S[0], S[1]) = dist.of(Distributed[Indexed, NormalDistribution])
    ((S[x], k), S[x[:k].as_boolean()]), S[x[k]] = eq_conditioned.of(Equal[Conditioned[Indexed]])
    return Distributed(Sum[i:k](x[i] ** 2), ChiSquaredDistribution(k))


@prove
def prove(Eq):
    from Axiom import Stats, Algebra, Calculus, Sets, Geometry

    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), real=True, random=True)
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(Equal(x[k] | x[:k], x[k]), Distributed(x[i], NormalDistribution(0, 1)))

    Eq.initial = Eq[2].subs(k, 1)

    Eq << Eq[1].subs(i, 0)

    Eq << Stats.Distributed.to.Distributed.ChiSquared.apply(Eq[-1])

    Eq.induct = Eq[2].subs(k, k + 1)

    Eq << Eq.induct.this.lhs.apply(Algebra.Sum.eq.Add.pop)

    y = Symbol(real=True, nonnegative=True)
    Eq << Stats.Distributed.of.Eq.Prob.apply(Eq[-1], y)

    Y = Symbol(Eq[-1].find(Sum))
    Eq.Y_def = Y.this.definition

    Eq << Eq[-1].subs(Eq.Y_def.reversed)

    Eq.eq_grad = Eq[-1].this.lhs.apply(Stats.Prob.eq.Grad)

    Eq << Stats.Eq_Conditioned.to.Eq.Conditioned.Sum.Square.apply(Eq[0], i=i, y=Y.var)

    Eq << Eq[-1].subs(Eq.Y_def.reversed)

    Eq << Stats.Eq_Conditioned.to.Eq.Mul.Prob.apply(Eq[-1])

    Eq << Eq[1].subs(i, k)

    Eq << Stats.Distributed.to.Eq.Prob.apply(Eq[-1])

    Eq << Eq.eq_grad.subs(Eq[-3], Eq[-1])

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.swap)

    Eq.eq_grad = Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.separate)

    Eq << Eq.eq_grad.find(Mul[~Integral]).this.find(LessEqual).apply(Algebra.Le.transport, lhs=0)

    Eq << Eq[-1].this.rhs.find(LessEqual).apply(Sets.LeSquare.equ.In.Interval)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.limits.absorb)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Mul.Bool)

    Eq << Eq[-1].this.rhs.find(LessEqual).apply(Algebra.Le.equ.Ge_0)

    Eq << Eq[-1].this.rhs.find(GreaterEqual) / 2

    Eq << Eq[-1].this.rhs.find(Integral).apply(Calculus.Integral.eq.Add.split, 0)

    Eq << Eq[-1].this.find(Integral[2]).apply(Calculus.Integral.limits.subs, x.var[k], -x.var[k])

    Eq << Eq[-1].this.find(-~Integral).apply(Calculus.Integral.eq.Neg)

    Eq << Eq[-1].this.find(Pow >= 0).apply(Algebra.Ge_0.st.Sqrt)

    Eq << Eq[-1].this.find(Add >= 0).apply(Algebra.Ge.transport, lhs=-1)

    Eq << Eq.eq_grad.subs(Eq[-1])

    Eq << Stats.Distributed.to.Eq.Prob.apply(Eq[2], Y.var)

    Eq << Eq[-1].subs(Eq.Y_def.reversed)

    Eq << Algebra.Eq.Cond.of.And.subs.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.eq.Integral)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.Mul.eq.Add)

    Eq << Eq[-1].this.find(Derivative[Bool]).apply(Calculus.Grad.Bool.eq.Zero)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.Integral.eq.Mul.Grad)

    Eq << Eq[-1].this.find(Bool ** 2).apply(Algebra.Square.eq.Bool)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Exp * Exp).args[-2:].apply(Algebra.Mul.eq.Exp)

    Eq << Eq[-1] * 2 ** (k / 2 + S.Half)

    Eq << Eq[-1].this.find(Pow * Pow).args[1:3].apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1] * (sqrt(S.Pi) * Gamma(k / 2))

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.absorb)

    t = Symbol(domain=Interval(0, pi / 2))
    Y = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.subs, Y, y * sin(t) ** 2)

    Eq << Eq[-1].this.find(-sin ** 2).args[2].apply(Geometry.Square.Sin.eq.Sub.Square.Cos)

    Eq << Eq[-1].this.find(Mul[One - cos ** 2]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Integral)().find(Abs[Cos]).simplify()

    Eq << Eq[-1].this.find(Mul ** Add).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.find(Integral)().find(Abs).simplify()

    Eq << Eq[-1].this.find(sin * Pow).apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.Sin.eq.Mul.gamma.wallis)

    Eq << Imply(Eq[2], Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], n=k, start=1)
    # https://www.asmeurer.com/blog/




if __name__ == '__main__':
    run()
# created on 2021-07-17
# updated on 2023-06-22
