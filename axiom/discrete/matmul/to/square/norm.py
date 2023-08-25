from util import *


@apply
def apply(self, swap=False):
    args = self.of(MatMul)
    size = len(args)
    assert not size & 1
    size //= 2
    x, y = args[:size], args[size:]
    if swap:
        x, y = y, x
    x = MatMul(*x)
    y = MatMul(*y)
    if y == ~x:
        ...
    elif len(x.shape) == 1:
        assert y.T == ~x

    return Equal(self, Norm(x) ** 2)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(x @ ~x)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.reducedSum.square.abs)

    Eq << Eq[-1].this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.reducedSum)

    


if __name__ == '__main__':
    run()
# created on 2023-06-24
