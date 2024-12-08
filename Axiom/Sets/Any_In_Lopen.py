from util import *


@apply
def apply(x, n=None):
    if n is None:
        n = x.generate_var(integer=True)
    assert x.is_real
    return Any[n](Element(n, Interval(x - 1, x, left_open=True)))


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(x, n)

    Eq << Eq[-1].this.expr.apply(Sets.In_Interval.of.And)

    Eq << Eq[-1].this.find(Greater) + 1

    Eq << Eq[-1].this.expr.apply(Sets.Gt.Le.of.In)

    Eq << Sets.Any_In_Ropen.apply(x, n)


if __name__ == '__main__':
    run()

# created on 2021-04-21
