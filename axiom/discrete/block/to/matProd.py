from util import *


@apply
def apply(n, m, b):
    i = Symbol(integer=True)

    return Equal(BlockMatrix(BlockMatrix(MatProduct[i:m](SwapMatrix(n, i, b[i])), ZeroMatrix(n)).T,
                             BlockMatrix(ZeroMatrix(n), 1)).T,
                             MatProduct[i:m](SwapMatrix(n + 1, i, b[i])))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(domain=Range(2, oo))
    m = Symbol(positive=True, integer=True, given=False)
    b = Symbol(integer=True, shape=(oo,), nonnegative=True)
    Eq << apply(n, m, b)

    Eq.initial = Eq[0].subs(m, 1)

    Eq.concatenate = discrete.block.swapMatrix.apply(n)

    * _, i, j = Eq.concatenate.rhs.args
    Eq << Eq.concatenate.subs(i, 0).subs(j, b[0]).T

    Eq.induct = Eq[0].subs(m, m + 1)

    Eq << Eq.induct.this.rhs.apply(discrete.matProd.to.matmul.pop_back)

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq << Eq.concatenate.subs(i, m).subs(j, b[m]).T

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.matProd.push_back)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=m, start=1)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-31
# updated on 2022-09-20
