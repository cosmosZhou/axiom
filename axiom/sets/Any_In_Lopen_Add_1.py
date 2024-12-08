from util import *


@apply
def apply(x, k=None):
    assert x.is_real
    if k is None:
        k = x.generate_var(integer=True, var='k')

    return Any[k](Element(x, Interval(k, k + 1, left_open=True)))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x = Symbol(real=True, given=True)
    Eq << apply(x)

    Eq << Algebra.Any.of.Cond.subs.apply(Eq[0], Eq[0].variable, Ceiling(x) - 1)

    Eq << Sets.In_Interval.of.And.apply(Eq[-1])

    Eq << Algebra.Gt_Sub_.Ceiling.One.apply(x)

    Eq << Algebra.Le_Ceiling.apply(x)


if __name__ == '__main__':
    run()
# created on 2018-10-29
