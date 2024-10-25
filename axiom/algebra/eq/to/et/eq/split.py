from util import *


@apply
def apply(given, index=None):
    lhs, rhs = given.of(Equal)
    from axiom.algebra.expr.to.block import split
    if index is None:
        if lhs.shape[0] == oo:
            index = 1
        else:
            index = -1

    if index < 0:
        index += lhs.shape[0]
    assert index < lhs.shape[0] and index > 0

    lhs = split(lhs, index)
    rhs = split(rhs, index)

    lhs0, lhs1 = lhs.of(BlockMatrix)
    rhs0, rhs1 = rhs.of(BlockMatrix)

    return Equal(lhs0, rhs0) & Equal(lhs1, rhs1)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n + 1,))
    y = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(x, y[:n + 1]))

    Eq << algebra.iff.of.et.infer.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.eq.then.et.eq.split)

    Eq << Eq[-1].this.lhs.apply(algebra.et.concat, 1, 0)





if __name__ == '__main__':
    run()
# created on 2023-03-22
# updated on 2023-05-19
