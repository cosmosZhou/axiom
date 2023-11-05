from util import *


@apply
def apply(self):
    (k, S[k + 1]), (k, S[1], n) = self.of(Sum[1 / (Expr * Expr)])
    n -= 1
    return Equal(self, 1 - 1 / (n + 1))


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[k:1:n + 1](1 / (k * (k + 1))))

    Eq << (1 / k - 1 / (k + 1)).this.apply(algebra.add.to.mul.together)

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.sub.telescope)
    #https://en.wikipedia.org/wiki/Telescoping_series



if __name__ == '__main__':
    run()
# created on 2023-08-17
