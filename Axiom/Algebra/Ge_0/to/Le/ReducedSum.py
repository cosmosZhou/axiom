from util import *


@apply
def apply(ge):
    x = ge.of(Expr >= ZeroMatrix)
    n, = x.shape
    assert x.is_real
    return x <= ReducedSum(x) * OneMatrix(*x.shape)


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(real=True, shape=(n,), given=True)
    Eq << apply(x >= ZeroMatrix(n))

    Eq << Algebra.Le.of.All.Le.apply(Eq[1])

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum)

    i = Eq[-1].lhs.index
    Eq << Eq[-1].find(Sum).this.apply(Algebra.Sum.eq.Add.split, cond={i})

    Eq << Algebra.Ge.to.All.Ge.apply(Eq[0], i)

    Eq << Algebra.Ge_0.to.Ge_0.Sum.apply(Eq[-1], (i, Range(n) - {i}))

    Eq << Algebra.Eq.Ge.to.Ge.Add.apply(Eq[-3], Eq[-1])

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this(i).find(Element).simplify()

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-03-25