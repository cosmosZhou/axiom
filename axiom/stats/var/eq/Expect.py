from util import *


@apply
def apply(self):
    expr, *limits = self.of(Variance)
    if expr.is_Conditioned:
        expr, given = expr.args
    else:
        given = None
    return Equal(self,
                 Expectation((expr - Expectation(expr, *limits, given=given)).outer_product(), *limits, given=given))

@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    n = Symbol(integer=True, positive=True)
    x, t = Symbol(real=True, random=True, shape=(n,))
    Eq << apply(Variance(x | t))

    Eq << Eq[0].lhs.this.apply(Stats.Var.eq.Cov)

    Eq << Eq[-1].this.rhs.apply(Stats.Cov.eq.Sub.Expect)

    Eq << Eq[0].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Stats.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul[-1]]]).apply(Stats.Expect.eq.Mul)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul[-1]]]).apply(Stats.Expect.eq.Mul)

    Eq << Eq[-1] + Eq[2].reversed

    Eq << Eq[-1].simplify()

    i = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[-1], i)

    j = Symbol(domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[-1], j)



if __name__ == '__main__':
    run()
# created on 2023-03-24
# updated on 2023-04-14
