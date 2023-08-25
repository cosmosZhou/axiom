from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[GreaterEqual])

    return GreaterEqual(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(All[i:n](GreaterEqual(f(i), g(i))))

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[2], cond=f(n) >= g(n))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push)

    Eq << Eq[-1].this.rhs.apply(algebra.ge.ge.imply.ge.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.sub.push)

    Eq << Eq[-1].this.find(Add[~Sum]).apply(algebra.sum.to.sub.push)

    Eq << Infer(Eq[2], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)


    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[2])




if __name__ == '__main__':
    run()

# created on 2019-01-13
# updated on 2023-04-23
