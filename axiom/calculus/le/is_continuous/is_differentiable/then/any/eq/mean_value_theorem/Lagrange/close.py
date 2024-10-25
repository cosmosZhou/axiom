from util import *


@apply
def apply(le, is_continuous, is_differentiable):
    a, b = le.of(LessEqual)
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.then.any.eq.Rolle import of_differentiable, of_continuous
    fz, (z, S[a], S[b]) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable, open=False)

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:Interval(a, b)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    from axiom.calculus.lt.is_continuous.is_differentiable.eq.then.any.eq.Rolle import is_differentiable
    from axiom.calculus.all_eq.then.all.any.eq.intermediate_value_theorem import is_continuous
    a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a <= b, is_continuous(f, a, b), is_differentiable(f, a, b, open=False))

    Eq << algebra.cond.of.et.infer.split.apply(Eq[-1], cond=b > a)

    Eq << Infer(b <= a, Equal(a, b), plausible=True)

    Eq << algebra.infer.of.ou.apply(Eq[-1]).reversed

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.of.et.subs)

    Eq << algebra.all.then.all.limits.restrict.apply(Eq[2], Interval(a, b, left_open=True, right_open=True))

    Eq << algebra.cond.then.infer.apply(Eq[1] & Eq[-1], cond=b > a)

    Eq << algebra.infer_et.then.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].reversed

    Eq << Eq[-1].this.rhs.apply(calculus.lt.is_continuous.is_differentiable.then.any.eq.mean_value_theorem.Lagrange)

    Eq << Eq[-1].this.rhs.apply(algebra.any.then.any.limits.relax, domain=Interval(a, b))




if __name__ == '__main__':
    run()

# created on 2020-04-29
# updated on 2023-08-26
