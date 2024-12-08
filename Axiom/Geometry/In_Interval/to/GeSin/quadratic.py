from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval(0, S.Pi / 2)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Axiom import Calculus, Geometry, Algebra, Sets

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi / 2)))

    @Function
    def f(x):
        return sin(x) - x * (1 - x / S.Pi)
    Eq << f(x).this.defun()

    Eq << Calculus.Eq.to.Eq.Grad.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.find(cos).apply(Geometry.Cos.eq.Sub.Square.Sin)

    Eq << Eq[-1] / 2

    Eq.eq_grad = Eq[-1].this.rhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[0], 2)

    Eq <<= Geometry.In_Interval.to.Ge_0.Sin.apply(Eq[-1]), Geometry.In_Interval.to.LeSin.Sqrt.apply(Eq[-1])

    Eq << Algebra.Ge.Le.to.Ge.trans.apply(Eq[-2], Eq[-1])

    Eq <<= Algebra.Ge_0.Ge_0.to.Ge_0.Add.apply(Eq[-1], Eq[-3]), Algebra.Le.to.Ge_0.apply(Eq[-2])

    Eq <<= Algebra.Ge_0.Ge_0.to.Ge_0.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Eq.Ge.to.Ge.trans.apply(Eq.eq_grad, Eq[-1]) * 2

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-1], (x, Interval(0, S.Pi / 2)))

    Eq << Calculus.All_Ge_0.to.All.Ge.monotony.right_close.apply(Eq[-1])

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.expr.apply(Algebra.Ge_0.to.Ge)

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
