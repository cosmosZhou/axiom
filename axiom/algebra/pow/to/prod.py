from util import *


@apply
def apply(self):
    base, exp = self.of(Pow)
    fn, *limits = base.of(Product)
    assert exp >= 0 or exp.is_integer
    return Equal(self, Product(fn ** exp, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    f = Function(real=True)
    k = Symbol(integer=True)
    n = Symbol(integer=True, given=False, positive=True)
    t = Symbol(integer=True, nonnegative=True)

    Eq << apply(Product[k:n](f(k)) ** t)

    Eq << Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.rhs.apply(algebra.prod.to.mul.split, cond={n})

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.split, cond={n})

    Eq << Eq[-1].this.lhs.apply(algebra.pow.to.mul.split.base)

    Eq << Eq[0] * Eq[-1].find(Pow)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-01-31
