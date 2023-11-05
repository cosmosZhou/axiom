from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    assert domain in Interval(0, S.Pi / 2)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from axiom import calculus, geometry, algebra, sets

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi / 2)))

    @Function
    def f(x):
        return sin(x) - x * (1 - x / S.Pi)
    Eq << f(x).this.defun()

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].this.find(cos).apply(geometry.cos.to.sub.square.sin)

    Eq << Eq[-1] / 2

    Eq.eq_grad = Eq[-1].this.rhs.apply(algebra.sub.square.to.mul)

    Eq << sets.el.imply.el.div.interval.apply(Eq[0], 2)

    Eq <<= geometry.el_interval.imply.ge_zero.sin.apply(Eq[-1]), geometry.el_interval.imply.sin_le.sqrt.apply(Eq[-1])

    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[-2], Eq[-1])

    Eq <<= algebra.ge_zero.ge_zero.imply.ge_zero.add.apply(Eq[-1], Eq[-3]), algebra.le.imply.ge_zero.apply(Eq[-2])

    Eq <<= algebra.ge_zero.ge_zero.imply.ge_zero.apply(Eq[-1], Eq[-2])

    Eq << algebra.eq.ge.imply.ge.transit.apply(Eq.eq_grad, Eq[-1]) * 2

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (x, Interval(0, S.Pi / 2)))

    Eq << calculus.all_ge_zero.imply.all_ge.monotony.right_close.apply(Eq[-1])

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.expr.apply(algebra.ge_zero.imply.ge)

    Eq << algebra.all.imply.infer.apply(Eq[-1])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
