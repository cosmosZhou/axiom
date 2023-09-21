from util import *


@apply
def apply(self):
    args = self.of(MatMul)
    size = len(args)
    assert not size & 1
    size //= 2
    x, y = args[:size], args[size:]
    x = MatMul(*x)
    y = MatMul(*y)
    if y == ~x:
        ...
    elif len(x.shape) == 1:
        assert y.T == ~x

    return Equal(self, ReducedSum(abs(x) ** 2))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(x @ ~x)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.mul.conj.to.square.abs)

    Eq << Eq[-1].this.rhs.simplify()




if __name__ == '__main__':
    run()
# created on 2023-06-23
