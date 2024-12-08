from util import *


@apply
def apply(le):
    lhs, rhs = le.of(Expr >= BlockMatrix)

    args = []
    for e in rhs:
        assert len(lhs.shape) <= len(e.shape)
        args.append(lhs >= e)

    return tuple(args)


@prove
def prove(Eq):
    from Axiom import Algebra

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(x >= BlockMatrix(a, b))

    Eq << Algebra.Ge.of.All.Ge.apply(Eq[0])

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[-1])

    Eq << Algebra.Ge.to.All.Ge.apply(Eq[1])

    i = Eq[-1].rhs.index
    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-1], (i, Range(-oo, n)), simplify=None)

    Eq.infer_lt = Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Algebra.Ge.to.All.Ge.apply(Eq[2])

    Eq << Eq[-1].subs(i, i - n)

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-1], (i, Range(n, oo)), simplify=None)

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Algebra.Imply.Imply.to.Or.apply(Eq.infer_lt, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-04-29
