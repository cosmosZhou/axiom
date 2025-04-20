from util import *


@apply
def apply(self, strict=False):
    if strict:
        cond = self > 0
    else:
        cond = self >= 0
    return Equal(self, Piecewise((relu(self), cond), (-relu(-self), True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Neuro

    x = Symbol(real=True)
    Eq << apply(x)

    Eq << Algebra.Expr.eq.Ite.apply(x, lower=S.Zero)

    Eq << Eq[-1].this.find(LessEqual).reversed

    Eq << Eq[-1].this.find(Max).apply(Neuro.Max.eq.Relu)

    Eq << Eq[-1].this.find(Min).apply(Neuro.Min.eq.Neg.Relu)





if __name__ == '__main__':
    run()
# created on 2021-12-25
