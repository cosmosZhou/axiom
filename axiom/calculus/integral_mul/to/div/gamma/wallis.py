from util import *


@apply
def apply(self):
    ((x, m), (x, n)), (x, S[0], S[pi / 2]) = self.of(Integral[Cos ** Expr * Sin ** Expr])
    m += 1
    n += 1
    
    return Equal(self, gamma(m / 2) * gamma(n / 2) / (2 * gamma((m + n) / 2)))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    #m is the inductive variable
    m = Symbol(integer=True, positive=True, given=False)
    #n is not an inductive variable
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True)
    Eq << apply(Integral[x:0:S.Pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)))

    Eq.one = Eq[0].subs(m, 1)

    Eq << Eq.one.this.lhs.apply(calculus.integral_sin.to.mul.gamma.wallis)

    Eq.induct = Eq[0].subs(m, m + 2)

    Eq << Eq.induct.this.lhs.expr.expand()

    Eq << Eq[-1].this.lhs.apply(calculus.integral.to.add.by_parts)

    
    Eq << Eq[-1] / (m / n)
    Eq << Eq[-1].this.rhs.expand(func=True)
    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], n, n + 2)
    Eq << Eq[-1].this.rhs.expand(func=True)
    Eq << Eq[-1].this.lhs.expand()
    Eq.two = Eq[0].subs(m, 2)
    Eq << Eq.two.this.lhs.apply(calculus.integral.limits.subs, sin(x), x)
    Eq << Eq[-1].this.lhs.apply(calculus.integral_pow.to.mul)
    Eq << Eq[-1].this.rhs.expand(func=True)
    Eq << Infer(Eq[0], Eq.induct, plausible=True)
    Eq << algebra.eq.eq.infer.imply.eq.induct.apply(Eq.one, Eq.two, Eq[-1], n=m, start=1)
    
    


if __name__ == '__main__':
    run()

# created on 2020-07-01
# updated on 2023-07-03
