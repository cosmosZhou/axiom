from util import *


@apply
def apply(n):
    i, j = Symbol(integer=True)

    return Equal(BlockMatrix([[SwapMatrix(n, i, j), ZeroMatrix(n)], [ZeroMatrix(n), S.One]]), SwapMatrix(n + 1, i, j))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(domain=Range(2, oo))
    Eq << apply(n)

    i, j = Eq[0].rhs.args
    _i = i.copy(domain=Range(n))
    _j = j.copy(domain=Range(n))
    W = Symbol(Eq[0].lhs._subs(i, _i)._subs(j, _j))
    V = Symbol(Eq[0].rhs._subs(i, _i)._subs(j, _j))
    Eq << W.this.definition

    Eq << V.this.definition

    h, k = Symbol(domain=Range(n + 1))
    Eq << (V[h, k].this.definition, W[h, k].this.definition)

    Eq <<= Eq[-1].this.rhs.apply(algebra.piece.to.kroneckerDelta), Eq[-2].this.rhs.apply(algebra.piece.to.kroneckerDelta)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].apply(algebra.eq.imply.eq.lamda, (k,), (h,))

    Eq << Eq[-1].subs(Eq[1], Eq[2])

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (_i,), (_j,))

    Eq << Eq[-1].reversed

    
    


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-30
# updated on 2022-01-06