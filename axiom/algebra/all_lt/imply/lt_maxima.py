from util import *


@apply
def apply(given): 
    (fx, M), *limits = given.of(All[Less])
    return Maxima(fx, *limits) < M


@prove
def prove(Eq):
    from axiom import algebra

    M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(All[x:a:b](f(x) < M))

    Eq << -Eq[0].this.expr

    Eq << algebra.all_gt.imply.gt_minima.apply(Eq[-1])

    Eq << Eq[-1].this.find(Minima).apply(algebra.minima.to.neg.maxima)
    Eq << -Eq[-1]

    
    


if __name__ == '__main__':
    run()
# created on 2019-06-06
# updated on 2021-09-30