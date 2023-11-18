from util import *


@apply
def apply(self):
    expr, *limits = self.of(Im[Sum])
    return Equal(self, Sum(Im(expr), *limits))


@prove
def prove(Eq):
    from axiom import algebra
    
    x = Symbol(real=True)
    f = Function(complex=True)
    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Im(Sum[k:n](f[k](x))))
    
    Eq << Eq[0].subs(n, n + 1)
    
    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.pop)
    
    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.to.add.pop)
    
    Eq << Infer(Eq[0], Eq[1], plausible=True)
    
    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n)


if __name__ == '__main__':
    run()
# created on 2023-10-02
