from util import *


@apply
def apply(given, x=None):
    S = given.of(Card > 0)
    n = Card(S)
    i = S.generate_var(integer=True)
    kwargs = S.etype.dict
    if 'shape' in kwargs:
        shape = (oo,) + kwargs['shape']
    else:
        shape = (oo,)
    kwargs.pop('shape', None)
    if x is None:
        x = S.generate_var(shape=shape, **kwargs)
    return Any[x[:n]](Equal(S, Cup[i:n]({x[i]})))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True, positive=True)
    s = Symbol(etype=dtype.integer[k], given=True)
    Eq << apply(Card(s) > 0)

    Eq << sets.gt.then.el.range.apply(Eq[0])

    m = Symbol(integer=True, positive=True)
    Eq << sets.el.then.any.eq.apply(Eq[-1], var=m)

    Eq << Eq[-1].this.expr.apply(sets.eq_card.then.any.et, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.then.eq.subs, swap=True, reverse=True, simplify=None, ret=1)

    Eq << algebra.any_et.then.any.limits_absorb.apply(Eq[-1], 1)

    Eq << sets.el.then.eq.intersect.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.any.limits.separate, simplify=None)

    Eq << Eq[-1].this.apply(algebra.any.to.ou.doit.setlimit)





if __name__ == '__main__':
    run()
# created on 2021-02-03
# updated on 2023-11-17
