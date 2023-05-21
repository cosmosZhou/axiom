from util import *


@apply
def apply(self):
    ((x, m), (x, n)), (x, S[0], S[pi / 2]) = self.of(Integral[Cos ** Expr * Sin ** Expr])
    m += 1
    n += 1
    return Equal(self, beta(m / 2, n / 2) / 2)


@prove
def prove(Eq):
    from axiom import calculus

    m, n = Symbol(integer=True, positive=True)
    x = Symbol(real=True)
    Eq << apply(Integral[x:0:S.Pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)))

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[-1].this.lhs.apply(calculus.integral_mul.to.div.gamma.wallis)

    
    


if __name__ == '__main__':
    run()

# created on 2020-07-02
# updated on 2023-04-30
