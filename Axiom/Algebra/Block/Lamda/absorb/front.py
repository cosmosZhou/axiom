from util import *


@apply
def apply(self, index=-1):
    print('use BlockMatrix.subs instead, which is more flexible')
    args = self.of(BlockMatrix)
    if index < 0:
        index += len(args)

    expr, *limits, (i, S[0], n) = args[index].of(Lamda)
    if limits:
        expr = Lamda(expr, *limits)
    front = args[index - 1]
    assert expr._subs(i, S.NegativeOne).simplify() == front
    args = args[:index - 1] + (Lamda[i:-1:n](expr).simplify(),) + args[index + 1:]

    return Equal(self, BlockMatrix(args))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(BlockMatrix([f(0), f(-1), Lamda[i:n](f(i))]))

    i = Symbol(domain=Range(n + 2))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[0], i)

    Eq << Algebra.Eq.of.Eq_0.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.Piece.eq.Piece)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.And.invert, 0)





if __name__ == '__main__':
    run()
# created on 2021-11-21
# updated on 2021-11-22