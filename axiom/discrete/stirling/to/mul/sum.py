from util import *


from sympy.functions.combinatorial.numbers import Stirling
@apply
def apply(self):
    n, k = self.of(Stirling)
    i = n.generate_var(k.free_symbols, integer=True)
    return Equal(self, Sum[i:k + 1]((-1) ** (k - i) * binomial(k, i) * i ** n) / factorial(k))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    k = Symbol(integer=True, nonnegative=True, given=False)
    n = Symbol(integer=True, nonnegative=True)
    Eq.hypothesis = apply(Stirling(n, k))

    Eq.induct = Eq.hypothesis.subs(k, k + 1)

    i = Eq.hypothesis.rhs.args[1].variable
    Eq << discrete.stirling.to.add.recurrence.apply(Stirling(n + 1, k + 1))

    Eq << Eq[-1].subs(Eq.hypothesis)

    y = Symbol(Lamda[n](Stirling(n, k + 1)))
    Eq << y[n].this.definition

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    j = Symbol(integer=True)
    #Eq << Eq[-1].this.apply(algebra.eq.rsolve.linear, j)
    Eq << algebra.eq.imply.eq.rsolve.apply(Eq[-1], j)

    Eq << Eq[-1].this.rhs.args[0].args[0].defun()

    Eq << Eq[-1].this.rhs.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.swap)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[Pow * Pow]).apply(algebra.sum.to.mul.series.geometric)

    Eq << Eq[-1].this.find(Sum).find(Expr ** -1).base.apply(algebra.add.to.mul.together)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.div.binom.increase)

    Eq << Eq[-1].this.find(Sum).expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.sub.push)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.binom.to.delta.zero)

    Eq << Eq[-1].this.find((~Pow) / Factorial).apply(algebra.pow.to.mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(Mul ** Symbol).apply(algebra.pow.to.mul.split.base)

    Eq.factor2mul = discrete.factorial.to.mul.apply(factorial(k + 1))

    Eq << Eq[-1].subs(Eq.factor2mul.reversed)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.sub.push)

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq.induct * factorial(k + 1)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.pop)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=k)





if __name__ == '__main__':
    run()
# created on 2020-10-13
# updated on 2023-08-26
