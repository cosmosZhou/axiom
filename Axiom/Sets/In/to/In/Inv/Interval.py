from util import *


@apply
def apply(given):
    x, self = given.of(Element)
    a, b = self.of(Interval)

    if a.is_positive:
        domain = Interval(1 / b, 1 / a, **self.kwargs_reversed)
    elif b.is_negative:
        domain = Interval(1 / a, 1 / b, **self.kwargs_reversed)
    elif a == 0 and self.left_open:
        domain = Interval(1 / b, oo, **self.kwargs_reversed)
    elif b == 0 and self.right_open:
        domain = Interval(-oo, 1 / a, **self.kwargs_reversed)

    return Element(1 / x, domain)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x, b = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq <<= Algebra.Ge.to.Le.Inv.apply(Eq[-2]), Algebra.Ge.to.Gt_0.apply(Eq[-2])

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[-1])

    Eq <<= Algebra.Gt_0.Le.to.Le.Mul.apply(Eq[-1], Eq[3]), Algebra.Gt.Le.to.Gt.trans.apply(Eq[-2], Eq[3])

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[-1])

    Eq <<= Algebra.Gt_0.Ge.to.Ge.Mul.apply(Eq[-1], Eq[-3])

    Eq << Sets.Ge.Le.to.In.Interval.apply(Eq[-1], Eq[4])


if __name__ == '__main__':
    run()
# created on 2020-06-21
