from util import *


@apply
def apply(self):
    x = self.of(Norm ** 2)
    n, = x.shape
    i = self.generate_var(integer=True)
    x = Lamda[i:n + 1](x[i]).simplify()
    return Equal(self, Norm(x) ** 2 - Abs(x[n]) ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(oo,))
    Eq << apply(Norm(x[:n]) ** 2)

    Eq << Eq[0].this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq << Eq[-1].this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.pop)


if __name__ == '__main__':
    run()
# created on 2023-06-25
# updated on 2023-07-01
