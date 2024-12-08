from util import *


@apply
def apply(le, is_continuous, is_differentiable):
    a, b = le.of(LessEqual)
    from Axiom.Calculus.Lt.is_continuous.is_differentiable.Eq.to.Any.Eq.Rolle import of_differentiable, of_continuous
    fz, (z, S[a], S[b]) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable, open=False)

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:Interval(a, b)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    from Axiom.Calculus.Lt.is_continuous.is_differentiable.Eq.to.Any.Eq.Rolle import is_differentiable
    from Axiom.Calculus.All_Eq.to.All.Any.Eq.intermediate_value_theorem import is_continuous
    a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a <= b, is_continuous(f, a, b), is_differentiable(f, a, b, open=False))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=b > a)

    Eq << Imply(b <= a, Equal(a, b), plausible=True)

    Eq << Algebra.Imply.of.Or.apply(Eq[-1]).reversed

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Algebra.All.to.All.limits.restrict.apply(Eq[2], Interval(a, b, left_open=True, right_open=True))

    Eq << Algebra.Cond.to.Imply.apply(Eq[1] & Eq[-1], cond=b > a)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].reversed

    Eq << Eq[-1].this.rhs.apply(Calculus.Lt.is_continuous.is_differentiable.to.Any.Eq.mean_value_theorem.Lagrange)

    Eq << Eq[-1].this.rhs.apply(Algebra.Any.to.Any.limits.relax, domain=Interval(a, b))




if __name__ == '__main__':
    run()

# created on 2020-04-29
# updated on 2023-08-26
