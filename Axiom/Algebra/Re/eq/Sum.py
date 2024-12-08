from util import *


@apply
def apply(self):
    expr, *limits = self.of(Re[Sum])
    return Equal(self, Sum(Re(expr), *limits))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    f = Function(complex=True)
    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Re(Sum[k:n](f[k](x))))

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Algebra.Imply.to.Eq.induct.apply(Eq[-1], n)




if __name__ == '__main__':
    run()
# created on 2023-10-02
