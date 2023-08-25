from util import *


@apply
def apply(self):
    len_shape = len(self.shape)
    import std
    reduced, args = std.array_split(self.of(ReducedSum[Add]), lambda arg : len(arg.shape) >= len_shape)
    reduced = (ReducedSum(arg).simplify() for arg in reduced)
    return Equal(self, Add(*reduced, *args), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(ReducedSum(x + y))

    Eq << Eq[0].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.reducedSum)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.reducedSum)

    


if __name__ == '__main__':
    run()
# created on 2022-04-02
from . import pop
from . import shift
from . import doit
