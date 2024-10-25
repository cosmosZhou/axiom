from util import *


@apply
def apply(lt_zero, el):
    a = lt_zero.of(Expr < 0)
    fa, R = el.of(Element)

    stop, start = R.of(Interval)
    if start.is_infinite:
        start = -start
    else:
        start /= a

    if stop.is_infinite:
        stop = -stop
    else:
        stop /= a

    return Element(fa / a, Interval(start, stop, left_open=R.right_open, right_open=R.left_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    t, x, a, b = Symbol(real=True)
    Eq << apply(t < 0, Element(x, Interval(a, b, left_open=True)))

    Eq << sets.el_interval.then.et.apply(Eq[1])

    Eq <<= algebra.lt_zero.gt.then.lt.div.apply(Eq[0], Eq[-2]), algebra.lt_zero.le.then.ge.div.apply(Eq[0], Eq[-1])

    Eq << sets.lt.ge.then.el.interval.apply(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-06-03
# updated on 2023-04-17
