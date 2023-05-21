from util import *


@apply
def apply(self):
    (fx, *limits), (gx, *S[limits]) = self.of(Sum - Sum)
    return Equal(self, Sum(fx - gx, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Sum[k:n](f(k)) - Sum[k:n](g(k)))

    Eq << Eq[0].this.find(-Sum).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.sum)


if __name__ == '__main__':
    run()
# created on 2018-08-09
