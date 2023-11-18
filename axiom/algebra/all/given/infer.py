from util import *



@apply
def apply(given):
    expr, *limits = given.of(All)
    return Infer(given.limits_cond.simplify(), expr)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(All[n:Equal(f[n], g[n])](Equal(f[n + 1], g[n + 1])))

    Eq << Eq[1].this.apply(algebra.infer.to.all, wrt=n)


if __name__ == '__main__':
    run()
# created on 2018-12-07
