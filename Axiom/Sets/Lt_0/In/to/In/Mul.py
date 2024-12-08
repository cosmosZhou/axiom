from util import *


@apply
def apply(is_positive, contains):
    a = is_positive.of(Expr < 0)
    fa, R = contains.of(Element)
    stop, start = R.of(Interval)
    if start.is_infinite:
        start = -start
    else:
        start *= a

    if stop.is_infinite:
        stop = -stop
    else:
        stop *= a

    return Element(fa * a, Interval(start, stop, left_open=R.right_open, right_open=R.left_open))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    t, x, a, b = Symbol(real=True)
    Eq << apply(t < 0, Element(x, Interval(a, b, left_open=True)))

    Eq << Sets.In_Interval.to.And.apply(Eq[1])

    Eq <<= Algebra.Lt_0.Gt.to.Lt.Mul.apply(Eq[0], Eq[-2]), Algebra.Lt_0.Le.to.Ge.Mul.apply(Eq[0], Eq[-1])

    Eq << Sets.Lt.Ge.to.In.Interval.apply(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-06-03
# updated on 2023-04-17
