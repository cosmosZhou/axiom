from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval.open(0, S.Pi)
    return x + sin(x) > x ** 2 * cot(x / 2)

@prove
def prove(Eq):
    from Axiom import Calculus, Geometry, Algebra, Sets

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval.open(0, S.Pi)))

    @Function(real=True)
    def f(x):
        return x + sin(x) - x ** 2 * cot(x / 2)
    Eq << f(x).this.defun()

    Eq << Calculus.Eq.to.Eq.Grad.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.find(cot ** 2).apply(Geometry.Square.Cot.eq.Sub.Square.Csc)

    Eq << Eq[-1].this.find(csc).apply(Geometry.Csc.eq.Inv.Sin)

    Eq << Eq[-1].this.find(cos).apply(Geometry.Cos.eq.Sub.double)

    Eq.eq_grad = Eq[-1].this.find(cot).apply(Geometry.Cot.eq.Div)

    t = Symbol(real=True)
    args = Eq.eq_grad.rhs.args
    y = args[0] + args[1] / x ** 2 * t ** 2 + args[2] / x * t + args[3] + args[4]
    Eq << Algebra.Add.eq.Add.square_completing.apply(y)

    Eq << Eq[-1].this.rhs.find(cos ** 2).apply(Geometry.Square.Cos.eq.Sub.Square.Sin)

    Eq << Eq[-1].subs(t, x)

    Eq << sin(x).this.apply(Geometry.Sin.eq.Mul.double)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.eq_grad = Algebra.Eq.Eq.to.Eq.trans.apply(Eq.eq_grad, Eq[-1])

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq.eq_grad)

    Eq << Algebra.Ne_0.to.Gt_0.Square.apply(Eq[-1])

    Eq << Sets.In_Interval.to.Gt.apply(Eq[0])

    Eq << Geometry.Gt_0.to.LtSin.apply(Eq[-1])

    Eq << Algebra.Lt.to.Gt_0.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Gt_0.Square.apply(Eq[-1])

    Eq << Algebra.Gt_0.Gt_0.to.Gt_0.Div.apply(Eq[-1], Eq[-5]) / 2

    Eq << Algebra.Eq.Gt.to.Gt.trans.apply(Eq[-1], Eq.eq_grad)

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-1], (x, Interval(0, S.Pi, right_open=True)))

    Eq << Calculus.All_Gt_0.to.All.Gt.monotony.right_open.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    print('logic error here:', f(0), 'is not defined at 0')
    Eq << Eq[-1].this.find(f).defun()

    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])

    Eq << Algebra.Gt_0.to.Gt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
