from util import *


@apply
def apply(given, var=None):
    x = given.of(Expr < 0)
    if var is None:
        var = given.generate_var(positive=True)
    else:
        assert not var.is_given
        assert var.domain == Interval.open(0, oo)
    return Any[var](Equal(x, -var))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(x < 0)

    Eq << Algebra.Lt_0.to.Eq.Abs.apply(Eq[0])

    Eq << -Eq[0].subs(-Eq[-1].reversed)

    Eq << Algebra.Any.of.Cond.subs.apply(Eq[1], Eq[1].variable, abs(x))

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq << -Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-01-17
