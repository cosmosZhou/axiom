from util import *


@apply
def apply(greater_than, _greater_than):
    x, a = greater_than.of(LessEqual)
    y, b = _greater_than.of(GreaterEqual)

    integer = x.is_integer and y.is_integer and a.is_integer and b.is_integer
    assert not integer
    return Subset(Interval(y, x), Interval(b, a))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, x, y = Symbol(real=True, given=True)
    Eq << apply(y <= b, x >= a)

    Eq << Sets.Subset.of.All_In.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(Sets.NotIn_Interval.to.Or)

    Eq << Algebra.Any.to.Any.And.limits.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Interval.to.And)

    # if self implies a False proposition, then self must be False
    Eq << Eq[-1].this.expr.apply(Algebra.Cond.Cond.Or.of.Or, simplify=False)

    Eq.any_ax, Eq.any_by = Any(Eq[-1].expr.args[0], *Eq[-1].limits, plausible=True), Any(Eq[-1].expr.args[1], *Eq[-1].limits, plausible=True)

    Eq <<= Algebra.Any_And.to.Any.limits_absorb.apply(Eq.any_ax, index=1), Algebra.Any_And.to.Any.limits_absorb.apply(Eq.any_by, index=2)

    Eq <<= Eq[-2].this.expr.apply(Algebra.Lt.Ge.to.Lt.trans), Eq[-1].this.expr.apply(Algebra.Gt.Le.to.Gt.trans)

    Eq <<= Eq[-2] & Eq[1], Eq[-1] & Eq[0]

    Eq << ~(~Eq.any_ax & ~Eq.any_by)




if __name__ == '__main__':
    run()

# created on 2021-05-17
# updated on 2023-05-20