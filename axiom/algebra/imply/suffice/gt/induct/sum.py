from util import *


@apply(given=None)
def apply(given, limit):
    xk, yk = given.of(Greater)
    k, a, b = limit
    assert xk._has(k)
    assert yk._has(k)

    return Suffice(All[k:a:b](xk > yk), Sum[k:a:b](xk) > Sum[k:a:b](yk))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    y, x = Symbol(shape=(oo,), integer=True)
    Eq << apply(x[k] > y[k], (k, 0, n))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[0], cond=x[n] > y[n])

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Eq[-1].this.rhs.apply(algebra.gt.gt.imply.gt.sum.push_back)

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

