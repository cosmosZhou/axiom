from util import *


@apply
def apply(self):
    from axiom.algebra.cond_piece.to.et.infer import piecewise_to_et
    return piecewise_to_et(self)



@prove
def prove(Eq):
    from axiom import algebra, sets

    x, p = Symbol(real=True, shape=())
    A, B = Symbol(etype=dtype.real)
    f, g, h = Function(shape=(), real=True)
    Eq << apply(Equal(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Eq[0].this.rhs.apply(algebra.piece.et.invert)

    Eq << algebra.cond.imply.et.infer.split.apply(Eq[-1], cond=Eq[0].find(Element))

    Eq << algebra.infer.imply.infer.subs.bool.apply(Eq[-2])

    Eq.former, Eq.latter = algebra.infer.imply.et.infer.split.apply(Eq[-1], cond=Eq[0].find(ExprCondPair[2]).cond)

    Eq << algebra.infer.imply.infer.subs.bool.apply(Eq.former)

    Eq << Eq[-1].this.lhs.apply(sets.el_complement.given.et, simplify=None)

    Eq << algebra.infer_et.imply.infer.et.subs.bool.apply(Eq[-1], index=1, invert=True)

    Eq << Eq[2].this.lhs.apply(sets.el_complement.imply.et, simplify=None)

    Eq << Eq.latter.this.find(Piecewise).apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.swap, 0)

    Eq << algebra.infer.imply.infer.subs.bool.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-04-29
