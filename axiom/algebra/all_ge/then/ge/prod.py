from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[GreaterEqual])
    assert rhs.is_nonnegative

    return GreaterEqual(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=False)
    i = Symbol(integer=True)
    g = Function(shape=(), real=True, nonnegative=True)
    f = Function(shape=(), real=True)
    Eq << apply(All[i:n](f(i) >= g(i)))

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Eq.induct.this.find(Product).apply(algebra.prod.to.mul.pop)

    Eq << Eq[-1].this.find(GreaterEqual[~Product]).apply(algebra.prod.to.mul.pop)

    Eq << algebra.infer.then.infer.et.both_sided.apply(Eq[2], cond=f(n) >= g(n))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.of.all.push)

    Eq << Eq[-1].this.rhs.apply(algebra.ge.ge.then.ge.mul)

    Eq << Infer(Eq[2], Eq.induct, plausible=True)

    Eq << algebra.infer.then.cond.induct.apply(Eq[-1], n=n, start=1)

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[0], Eq[2])





if __name__ == '__main__':
    run()

# created on 2019-01-12
# updated on 2023-04-23
