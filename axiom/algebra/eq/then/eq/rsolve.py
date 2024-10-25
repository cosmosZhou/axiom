from util import *


@apply
def apply(self, k=None):
    (x, n), fx = self.of(Equal[Indexed])
    if n.is_Add:
        offset, n = n.of(Add)
    else:
        offset = 0

    c, item = fx.of(Expr * x[n + offset - 1] + Expr)
    if k is None:
        k = self.generate_var(integer=True)

    assert c.is_nonzero
    return Equal(x[n], x[0] * c ** n + Sum[k:n](item._subs(n, k) * c ** (n - k - 1)))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    c = Symbol(real=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    h = Function(real=True)
    Eq << apply(Equal(x[n + 1], x[n] * c + h(n)), k)

    Eq << Eq[0] / c ** (n + 1)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Symbol * Pow).args[:2].apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].subs(n, k)

    Eq << algebra.ou.then.all.apply(Eq[-1], 1)

    Eq << algebra.eq.then.eq.sum.apply(Eq[-1], (k, 0, n))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.subs.offset, -1)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.sub.unshift)

    Eq << Eq[-1] + x[0]

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.pop)

    Eq << Eq[-1] * c ** n

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)





if __name__ == '__main__':
    run()
# created on 2021-09-29
# updated on 2023-06-17
