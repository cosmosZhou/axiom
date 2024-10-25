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
    from axiom import sets, algebra

    a, b, x, y = Symbol(real=True, given=True)
    Eq << apply(y <= b, x >= a)

    Eq << sets.subset.of.all_el.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(sets.notin_interval.then.ou)

    Eq << algebra.any.then.any.et.limits.single_variable.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el_interval.then.et)

    # if self implies a False proposition, then self must be False
    Eq << Eq[-1].this.expr.apply(algebra.cond.cond.ou.of.ou, simplify=False)

    Eq.any_ax, Eq.any_by = Any(Eq[-1].expr.args[0], *Eq[-1].limits, plausible=True), Any(Eq[-1].expr.args[1], *Eq[-1].limits, plausible=True)

    Eq <<= algebra.any_et.then.any.limits_absorb.apply(Eq.any_ax, index=1), algebra.any_et.then.any.limits_absorb.apply(Eq.any_by, index=2)

    Eq <<= Eq[-2].this.expr.apply(algebra.lt.ge.then.lt.trans), Eq[-1].this.expr.apply(algebra.gt.le.then.gt.trans)

    Eq <<= Eq[-2] & Eq[1], Eq[-1] & Eq[0]

    Eq << ~(~Eq.any_ax & ~Eq.any_by)




if __name__ == '__main__':
    run()

# created on 2021-05-17
# updated on 2023-05-20
