from util import *


@apply
def apply(ge, *limits):
    fx, gx = ge.of(GreaterEqual)
    for v, *ab in limits:
        if v.is_random:
            fx = fx._subs(v.var, v)
            gx = gx._subs(v.var, v)
    return Expectation(fx, *limits) >= Expectation(gx, *limits)

@prove
def prove(Eq):
    from axiom import stats, algebra, calculus

    x = Symbol(real=True, random=True)
    f, g = Function(real=True)
    Eq << apply(f(x.var) >= g(x.var), (x,))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.integral)

    Eq << stats.then.ge_zero.prob.apply(Eq[-1].find(Probability))

    Eq << algebra.ge_zero.ge.then.ge.mul.apply(Eq[-1], Eq[0])

    Eq << calculus.ge.then.ge.integral.apply(Eq[-1], (x.var,))




if __name__ == '__main__':
    run()
# created on 2023-04-04
