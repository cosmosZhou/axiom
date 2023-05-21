from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Greater])
    for limit in limits:
        x, domain = limit.coerce_setlimit()
        assert domain.is_finiteset
    
    assert rhs.is_positive

    return Greater(Product(lhs, *limits).simplify(), Product(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), real=True, positive=True)
    Eq << apply(All[i:n](f(i) > g(i)))

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq.induct = Eq[2].subs(n, n + 1)

    Eq << Eq.induct.this.find(Product).apply(algebra.prod.to.mul.pop)

    Eq << Eq[-1].this.find(Greater[~Product]).apply(algebra.prod.to.mul.pop)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[2], cond=f(n) > g(n))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push)

    Eq << Eq[-1].this.rhs.apply(algebra.gt.gt.imply.gt.mul)

    Eq << Infer(Eq[2], Eq.induct, plausible=True)
    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)
    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[2])
    
    


if __name__ == '__main__':
    run()

# created on 2019-01-20
# updated on 2023-04-23
