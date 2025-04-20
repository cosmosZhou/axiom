from util import *


@apply
def apply(self, var=None, swap=False):
    (x, y), n = self.of(Pow[Add])
    if var is None:
        k = Symbol(integer=True)
    else:
        k = var
    assert n >= 0
    if swap:
        x, y = y, x
    return Equal(self, Sum[k:n + 1](binomial(n, k) * x ** k * y ** (n - k)))


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete, Logic

    x, y = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply((x + y) ** n)

    Eq.induct = Eq[-1].subs(n, n + 1)

    Eq << Eq[-1] * (x + y)

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul.eq.Sum)

    Eq << Eq[-1].this.rhs.expr.expand()

    Eq << Eq[-1].this.rhs.expr.powsimp()

    (k, *_), *_ = Eq[-1].rhs.limits
    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Sum.limits.subs.offset, -1)

    Eq << Discrete.Binom.eq.Add.Pascal.apply(Binomial(n + 1, k))

    Eq << Algebra.Cond.given.And.subs.apply(Eq.induct, *Eq[-1].args)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.Mul.eq.Add)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.Imp.induct.apply(Eq[-1], n=n)





if __name__ == '__main__':
    run()

# created on 2020-10-10
# updated on 2022-01-15
