from util import *


@apply
def apply(self, pivot=-1, i=None):
    args, (k, S[0], n) = self.of(Sum[Mul])
    n -= 1
    assert n >= 0
    fk, gk = std.array_split(args, pivot)
    fk = Mul(*fk)
    gk = Mul(*gk)
    if i is None:
        i = self.generate_var(integer=True, excludes={k, n})
    return Equal(self, fk._subs(k, S.Zero) * Sum[k:n + 1](gk) + Sum[k:n]((fk._subs(k, k + 1) - fk) * Sum[i:k + 1:n + 1](gk._subs(k, i))))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True)
    i, k = Symbol(integer=True)
    f, g = Function(real=True)
    Eq << apply(Sum[k:n + 1](f(k) * g(k)), i=i)

    Eq << Eq[0].this.rhs.find(Sum[~Mul]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum[Add]).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.subs.offset, -1)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.sub.unshift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.rhs.args[1:].apply(algebra.add.to.sum)

    Eq << Eq[-1].this.find(Mul - Mul).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.rhs.find(Sum)().find(~Sum - Sum).apply(algebra.sum.to.add.shift)





if __name__ == '__main__':
    run()
# created on 2023-06-02
# updated on 2023-06-03
from . import Newton_series
