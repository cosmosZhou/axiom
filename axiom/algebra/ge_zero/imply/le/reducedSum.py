from util import *


@apply
def apply(ge):
    x = ge.of(Expr >= ZeroMatrix)
    n, = x.shape
    assert x.is_real
    return x <= ReducedSum(x) * OneMatrix(*x.shape)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(real=True, shape=(n,), given=True)
    Eq << apply(x >= ZeroMatrix(n))

    Eq << algebra.le.given.all.le.apply(Eq[1])

    Eq << Eq[-1].this.find(ReducedSum).apply(algebra.reducedSum.to.sum)

    i = Eq[-1].lhs.index
    Eq << Eq[-1].find(Sum).this.apply(algebra.sum.to.add.split, cond={i})

    Eq << algebra.ge.imply.all.ge.apply(Eq[0], i)

    Eq << algebra.ge_zero.imply.ge_zero.sum.apply(Eq[-1], (i, Range(n) - {i}))

    Eq << algebra.eq.ge.imply.ge.add.apply(Eq[-3], Eq[-1])

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this(i).find(Element).simplify()

    Eq << Eq[-1].reversed

    
    


if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-03-25
