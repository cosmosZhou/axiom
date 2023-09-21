from util import *


@apply
def apply(self, swap=False):
    x = self.of(Norm ** 2)
    if swap:
        rhs = ~x @ x
    else:
        rhs = x @ ~x
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(Norm(x) ** 2)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.square.norm)

    


if __name__ == '__main__':
    run()
# created on 2023-06-24
