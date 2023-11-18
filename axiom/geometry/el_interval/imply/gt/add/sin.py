from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval.open(0, S.Pi)
    return x + sin(x) > x ** 2 * cot(x / 2)

@prove
def prove(Eq):
    from axiom import calculus, geometry, algebra, sets

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval.open(0, S.Pi)))

    @Function(real=True)
    def f(x):
        return x + sin(x) - x ** 2 * cot(x / 2)
    Eq << f(x).this.defun()

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].this.find(cot ** 2).apply(geometry.square.cot.to.sub.square.csc)

    Eq << Eq[-1].this.find(csc).apply(geometry.csc.to.inverse.sin)

    Eq << Eq[-1].this.find(cos).apply(geometry.cos.to.sub.double)

    Eq.eq_grad = Eq[-1].this.find(cot).apply(geometry.cot.to.div)

    t = Symbol(real=True)
    args = Eq.eq_grad.rhs.args
    y = args[0] + args[1] / x ** 2 * t ** 2 + args[2] / x * t + args[3] + args[4]
    Eq << algebra.poly.square_completing.apply(y)

    Eq << Eq[-1].this.rhs.find(cos ** 2).apply(geometry.square.cos.to.sub.square.sin)

    Eq << Eq[-1].subs(t, x)

    Eq << sin(x).this.apply(geometry.sin.to.mul.double)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.eq_grad = algebra.eq.eq.imply.eq.transit.apply(Eq.eq_grad, Eq[-1])

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq.eq_grad)

    Eq << algebra.ne_zero.imply.gt_zero.square.apply(Eq[-1])

    Eq << sets.el_interval.imply.gt.apply(Eq[0])

    Eq << geometry.gt_zero.imply.sin_lt.apply(Eq[-1])

    Eq << algebra.lt.imply.gt_zero.apply(Eq[-1])

    Eq << algebra.gt_zero.imply.gt_zero.square.apply(Eq[-1])

    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.div.apply(Eq[-1], Eq[-5]) / 2

    Eq << algebra.eq.gt.imply.gt.transit.apply(Eq[-1], Eq.eq_grad)

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (x, Interval(0, S.Pi, right_open=True)))

    Eq << calculus.all_gt_zero.imply.all.gt.monotony.right_open.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2])

    print('logic error here:', f(0), 'is not defined at 0')
    Eq << Eq[-1].this.find(f).defun()

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.gt_zero.imply.gt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-10-03
