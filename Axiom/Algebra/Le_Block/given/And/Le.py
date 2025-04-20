from util import *


@apply
def apply(le):
    lhs, rhs = le.of(Expr <= BlockMatrix)

    args = []
    for e in rhs:
        assert len(lhs.shape) <= len(e.shape)
        args.append(lhs <= e)

    return tuple(args)


@prove
def prove(Eq):
    from Axiom import Algebra, Logic

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(x <= BlockMatrix(a, b))

    Eq << Algebra.Le.given.All.Le.apply(Eq[0])

    Eq << Logic.Cond_Ite__Ite.given.And.ou.OrAndS.apply(Eq[-1])

    Eq << Algebra.All.Le.of.Le.apply(Eq[1])

    i = Eq[-1].rhs.index
    Eq << Algebra.All.of.Cond.restrict.apply(Eq[-1], (i, Range(-oo, n)), simplify=None)

    Eq.infer_lt = Logic.Imp.of.All.apply(Eq[-1])

    Eq << Algebra.All.Le.of.Le.apply(Eq[2])

    Eq << Eq[-1].subs(i, i - n)

    Eq << Algebra.All.of.Cond.restrict.apply(Eq[-1], (i, Range(n, oo)), simplify=None)

    Eq << Logic.Imp.of.All.apply(Eq[-1])

    Eq << Logic.Or.of.Imp.Imp.apply(Eq.infer_lt, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-04-29
