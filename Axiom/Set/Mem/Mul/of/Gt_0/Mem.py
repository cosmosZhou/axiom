from util import *


@apply
def apply(is_positive, contains):
    a = is_positive.of(Expr > 0)
    fa, R = contains.of(Element)
    start, stop = R.of(Interval)
    if not start.is_infinite:
        start *= a

    if not stop.is_infinite:
        stop *= a

    return Element(fa * a, R.copy(start=start, stop=stop))


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    t, x, a, b = Symbol(real=True)
    Eq << apply(t > 0, Element(x, Interval(a, b, left_open=True)))

    Eq << Set.And.of.Mem_Icc.apply(Eq[1])

    Eq <<= Algebra.GtMul.of.Gt_0.Gt.apply(Eq[0], Eq[-2]), Algebra.LeMul.of.Gt_0.Le.apply(Eq[0], Eq[-1])

    Eq << Set.Mem.Icc.of.Gt.Le.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-04-21
