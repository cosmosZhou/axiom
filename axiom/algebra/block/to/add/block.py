from util import *


@apply
def apply(self, pivot=-1):
    assert self.is_BlockMatrix
    if not isinstance(pivot, (list, tuple)):
        pivot = [pivot] * len(self.args)
    former, latter = zip(*([Add(*s) for s in std.array_split(expr.of(Add), pivot)] for expr, pivot in zip(self.args, pivot)))
    axis = self.axis
    return Equal(self, Add(BlockMatrix[axis](*former), BlockMatrix[axis](*latter), evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    A, B, C, D = Symbol(real=True, shape=(m, n))
    Eq << apply(BlockMatrix(A + C, B + D))

    Eq << Eq[0].this.rhs.apply(algebra.add.block.to.block)





if __name__ == '__main__':
    run()
# created on 2021-12-30
# updated on 2023-06-08
