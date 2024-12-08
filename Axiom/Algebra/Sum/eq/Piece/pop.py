from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Sum)
    assert i.is_integer
    back = function._subs(i, b - 1)
    return Equal(self, Piecewise((Add(Sum[i:a:b - 1](function), back), a <= b - 1), (0, True)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    i, n = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[i:n + 1](f(i)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={n})

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Piece)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.equ.And)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap)

    Eq << (n < 0).this.apply(Algebra.Lt.to.Eq_.Sum.Zero, Eq[-1].find(Sum))

    Eq << Algebra.Imply.to.Eq.Piece.apply(Eq[-1], Eq[-2].lhs)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.swap)
    Eq << Eq[-1].this.find(GreaterEqual).reversed


if __name__ == '__main__':
    run()
# created on 2020-03-25
