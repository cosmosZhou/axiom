from util import *


@apply
def apply(piecewise, i=0, offset=1, evaluate=False):
    [*ec] = piecewise.of(Piecewise)

    _, cond = ec[i]
    assert offset > 0
    j = i + offset

    expr_next, cond_next = ec[j]
    cond_next &= cond.invert()

    ec[j] = (expr_next, cond_next)

    if ec[-1][1]:
        ...
    else:
        ec[-1][1] = True

    return Equal(piecewise, piecewise.func(*ec, evaluate=evaluate))


@prove
def prove(Eq):
    from Axiom import Algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,))
    A, B = Symbol(etype=dtype.real[k])
    g, f, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((g(x), Element(x, A)), (f(x), NotElement(x, B)), (h(x), True)))

    p = Symbol(Eq[0].lhs)
    Eq << p.this.definition

    Eq << Algebra.Cond_Piece.to.Or.apply(Eq[-1])

    Eq << Algebra.Or.to.Eq.Piece.apply(Eq[-1], wrt=p)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, 0)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, 0)
    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[1], Eq[-1])





if __name__ == '__main__':
    run()

# created on 2018-01-30
# updated on 2023-05-20
