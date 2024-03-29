from util import *


@apply
def apply(self):
    arg, *limits = self.of(Sum[Im])
    
    return Equal(self, Im(Sum(arg, *limits)))


@prove
def prove(Eq):
    from axiom import algebra
    
    n = Symbol(integer=True, nonnegative=True, given=False)
    z = Symbol(complex=True, shape=(oo,))
    k = Symbol(integer=True)
    Eq << apply(Sum[k:n](Im(z[k])))
    
    Eq << Eq[0].subs(n, n + 1)
    
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.pop)
    
    Eq << Eq[-1].this.rhs.arg.apply(algebra.sum.to.add.pop)
    
    Eq << Infer(Eq[0], Eq[1], plausible=True)
    
    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n, 0)


if __name__ == '__main__':
    run()
# created on 2023-06-03
