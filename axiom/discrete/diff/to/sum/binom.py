from util import *


@apply
def apply(self, k=None):
    fx, (x, n) = self.of(Difference)
    if k is None:
        k = fx.generate_var(x.free_symbols | n.free_symbols, integer=True)
    return Equal(self, Sum[k:n + 1]((-1) ** (n - k) * binomial(n, k) * fx.subs(x, x + k)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    f = Function(real=True)
    x = Symbol(real=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Difference(f(x), (x, n)))

    Eq.initial = Eq[0].subs(n, 0)

    Eq << Eq.initial.this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(discrete.diff.split, 1)

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << Eq[-1].this.lhs.apply(discrete.diff.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={0})

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.split, cond={n + 1})

    Eq.hypothesis = algebra.cond.then.cond.subs.apply(Eq[0], x, x + 1)

    Eq << Eq.hypothesis - Eq[0]

    i = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.subs.offset, -1)

    Eq << Eq[-1].this.find(-Sum).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.to.add.split, cond={n + 1})

    Eq.split = Eq[-1].this.find(Sum).apply(algebra.sum.to.add.split, cond={0})

    Eq << Add(*Eq.split.rhs.args[2:]).this.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.expr.collect(Mul(*Eq[-1].rhs.expr.args[0].args[::2]))

    Eq << discrete.binom.to.add.Pascal.apply(Binomial(n + 1, i))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.split.subs(Eq[-1])

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.eq.infer.then.eq.induct.apply(Eq.initial, Eq[-1], n=n)





if __name__ == '__main__':
    run()

# created on 2020-10-10
# updated on 2023-06-03
