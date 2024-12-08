from util import *


@apply
def apply(self):
    from Axiom.Algebra.Cond_Piece.equ.And.Imply import piecewise_to_et
    return piecewise_to_et(self)



@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, p = Symbol(real=True, shape=())
    A, B = Symbol(etype=dtype.real)
    f, g, h = Function(shape=(), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Eq[0].this.rhs.apply(Algebra.Piece.And.invert)

    Eq << Algebra.Cond.to.And.Imply.split.apply(Eq[-1], cond=Eq[0].find(Element))

    Eq << Algebra.Imply.to.Imply.subs.Bool.apply(Eq[-2])

    Eq.former, Eq.latter = Algebra.Imply.to.And.Imply.split.apply(Eq[-1], cond=Eq[0].find(ExprCondPair[2]).cond)

    Eq << Algebra.Imply.to.Imply.subs.Bool.apply(Eq.former)

    Eq << Eq[-1].this.lhs.apply(Sets.In_Complement.of.And, simplify=None)

    Eq << Algebra.Imply_And.to.Imply.And.subs.Bool.apply(Eq[-1], index=1, invert=True)

    Eq << Eq[2].this.lhs.apply(Sets.In_Complement.to.And, simplify=None)

    Eq << Eq.latter.this.find(Piecewise).apply(Algebra.Piece.swap, 1)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.swap, 0)

    Eq << Algebra.Imply.to.Imply.subs.Bool.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-04-29
