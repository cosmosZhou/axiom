from util import *


@apply
def apply(given, *limits):
    fx = given.of(Expr >= 0)
    for limit in limits:
        x = limit[0]
        assert fx._has(x)
        assert not x.is_given
        assert not x.is_integer
        x, domain, *dir = Tuple(*limit).coerce_setlimit()
        if dir:
            dir, = dir
            assert dir > 0
        domain_defined = fx.domain_defined(x)
        assert domain in domain_defined

    return Integral(fx, *limits) >= 0


@prove
def prove(Eq):
    from axiom import calculus, algebra

    t = Symbol(real=True, positive=True)
    x = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(f(x) >= 0, (x, 0, t))

    Eq << Eq[1].this.find(Integral).apply(calculus.integral.to.limit.maxima.Darboux)

    Eq << Eq[-1] / t

    limits = Eq[-1].find(Sum).limits
    Eq << algebra.cond.then.all.restrict.apply(Eq[0], *Eq[-1].find(Maxima).limits)

    Eq << algebra.all_ge.then.maxima_ge.apply(Eq[-1])

    Eq << algebra.cond.then.all.restrict.apply(Eq[-1], *limits)

    Eq << algebra.all_ge.then.ge.sum.apply(Eq[-1])

    [k, S[0], n], = limits
    Eq << Eq[-1] / n

    Eq << calculus.ge.then.ge.limit.apply(Eq[-1], (n, oo))



if __name__ == '__main__':
    run()
# created on 2023-03-25
