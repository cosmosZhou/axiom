from util import *


@apply
def apply(self):
    cond, *limits = self.of(Any)
    from axiom.algebra.cond_piece.to.et.infer import piecewise_to_et
    args = piecewise_to_et(cond)
    infers = []
    for eq in args:
        p, q = eq.of(Infer)
        q = Any(q, *limits).simplify()
        infers.append(Infer(p, q))

    return tuple(infers)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n, n))
    i, j = Symbol(integer=True)
    p, q, r = Function(real=True, shape=())
    Eq << apply(Any[x](Equal(x[i, j], Piecewise((p(x), j < i), (q(x), j > i), (r(x), True)))))

    Eq << Eq[0].this.expr.apply(algebra.cond_piece.given.et.infer)

    Eq << algebra.any_et.given.et.infer.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-07-01
