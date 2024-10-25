from util import *


@apply
def apply(le):
    lhs, rhs = le.of(Expr > BlockMatrix)

    args = []
    for e in rhs:
        assert len(lhs.shape) <= len(e.shape)
        args.append(lhs > e)

    return tuple(args)


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(x > BlockMatrix(a, b))

    Eq << algebra.gt.then.all.gt.apply(Eq[0])

    Eq << algebra.cond_piece.then.ou.apply(Eq[-1])

    Eq << algebra.ou.then.et.infer.apply(Eq[-1])

    Eq <<= algebra.infer.then.all.single_variable.apply(Eq[-2], simplify=None), algebra.infer.then.all.single_variable.apply(Eq[-1], simplify=None)

    Eq <<= algebra.all.then.all.limits.restrict.apply(Eq[-2], domain=Range(0, n), simplify=None), algebra.all.then.all.limits.restrict.apply(Eq[-1], domain=Range(n, m + n), simplify=None)

    Eq << algebra.all_gt.then.gt.lamda.apply(Eq[-2])

    Eq << algebra.all_gt.then.gt.lamda.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-04-01
# updated on 2023-04-29
