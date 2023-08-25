from util import *


@apply
def apply(self, *, simplify=True):
    (ft, (t, a, b)), (x, S[1]) = self.of(Derivative[Integral])
    criteria = 1
    if b._has(x):
        if b.is_continuous(x):
            ...
        else:
            cond = Element(x, b.domain_defined(x, real=True)).simplify()
            criteria = Bool(cond)
        assert not a._has(x)
        dfx = Derivative[x](b)
        ft = ft._subs(t, b)
    elif a._has(x):
        assert a.is_continuous(x)
        assert not b._has(x)
        dfx = Derivative[x](a)
        ft = -ft._subs(t, a)

    if simplify:
        dfx = dfx.simplify()
    assert ft.is_continuous(t)
    return Equal(self, ft * dfx * criteria)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x, t, a = Symbol(real=True)
    f, h = Function(real=True, continuous=True)
    Eq << apply(Derivative[x](Integral[t:a:h(x)](f(t))))

    Eq << Eq[0].this.lhs.apply(calculus.grad.to.limit)

    epsilon = Eq[-1].lhs.variable
    Eq << Eq[-1].this.find(Add).apply(calculus.sub.to.integral)

    Eq << calculus.imply.is_continuous.interval.apply(*Eq[-1].find(Integral).args)

    Eq << calculus.is_continuous.imply.any_eq.interval01.mean_value_theorem.apply(Eq[-1], 'lamda')

    Eq.exists = Eq[-1].this.expr.apply(calculus.eq.imply.eq.limit.div, epsilon)

    Eq.limit_f = Equal(Limit[epsilon:0](Eq.exists.expr.rhs.find(f)), f(h(x)), plausible=True)

    Eq << Eq.limit_f.this.lhs.apply(calculus.limit.to.expr.continuity)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[0].rhs.find(Derivative).this.apply(calculus.grad.to.limit, epsilon).reversed

    Eq << calculus.eq_limit.eq_limit.imply.eq_limit.mul.apply(Eq[-1], Eq.limit_f)

    Eq << Eq.exists.this.expr.subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-05-05
# updated on 2023-06-19
