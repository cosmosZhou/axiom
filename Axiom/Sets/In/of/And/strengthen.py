from util import *


@apply
def apply(imply, lower=None, upper=None, strict=False):
    x, interval = imply.of(Element)
    a, b = interval.of(Interval)
    if upper is None:
        if strict:
            assert interval.right_open
            return Element(x, Interval(a, lower, left_open=interval.left_open)), lower < b
        return Element(x, interval.copy(start=a, stop=lower)), lower <= b
    else:
        if strict:
            assert interval.left_open
            return Element(x, Interval(upper, b, right_open=interval.right_open)), a < upper
        return Element(x, interval.copy(start=upper, stop=b)), a <= upper

@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    x = Symbol(complex=True, given=True)
    a, b, c = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)), c, strict=True)

    Eq << Sets.In_Interval.of.And.apply(Eq[0])

    Eq << Sets.In_Interval.to.And.apply(Eq[1])

    Eq << Algebra.Lt.Le.to.Lt.trans.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-29
