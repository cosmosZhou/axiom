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
    from Axiom import Discrete, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    Eq << apply(x @ ~x)

    Eq << Eq[-1].this.lhs.apply(Discrete.Dot.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Mul.Conj.eq.Square.Abs)

    Eq << Eq[-1].this.rhs.simplify()




if __name__ == '__main__':
    run()
# created on 2023-06-23