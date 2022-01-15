from util import *


@apply
def apply(self, k):
    f, (j, S[0], n), (i, S[0], m) = self.of(Lamda)

    A = Lamda[i:m, j:k](f).simplify()
    B = Lamda[i:m, j:n - k](f._subs(j, j + k))

    return Equal(self, BlockMatrix([A, B]).T, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(n))
    f = Function(real=True)
    Eq << apply(Lamda[j:n, i:m](f(i, j)), k)

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.apply(algebra.lamda.to.block.split, k)





if __name__ == '__main__':
    run()
# created on 2019-10-22
# updated on 2021-11-22