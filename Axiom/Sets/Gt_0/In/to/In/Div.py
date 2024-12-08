from util import *


@apply
def apply(is_positive, contains):
    a = is_positive.of(Expr > 0)
    fa, R = contains.of(Element)
    start, stop = R.of(Interval)
    if not R.start.is_infinite:
        start /= a

    if not R.stop.is_infinite:
        stop /= a

    return Element(fa / a, R.copy(start=start, stop=stop))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    t, x, a, b = Symbol(real=True)
    Eq << apply(t > 0, Element(x, Interval(a, b, left_open=True)))

    Eq << Sets.In_Interval.to.And.apply(Eq[1])

    Eq <<= Algebra.Gt_0.Gt.to.Gt.Div.apply(Eq[0], Eq[-2]), Algebra.Gt_0.Le.to.Le.Div.apply(Eq[0], Eq[-1])

    Eq << Sets.Gt.Le.to.In.Interval.apply(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-06-19
# updated on 2023-04-17
