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
    from Axiom import Set, Algebra

    k = Symbol(integer=True, positive=True)
    s = Symbol(etype=dtype.integer[k], given=True)
    Eq << apply(Card(s) > 0)

    Eq << Set.Mem.Range.of.Gt.apply(Eq[0])

    m = Symbol(integer=True, positive=True)
    Eq << Set.Any.Eq.of.Mem.apply(Eq[-1], var=m)

    Eq << Eq[-1].this.expr.apply(Set.Any.And.of.Eq_Card, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.of.Eq.Eq.subs, swap=True, reverse=True, simplify=None, ret=1)

    Eq << Algebra.Any.of.Any_And.limits_absorb.apply(Eq[-1], 1)

    Eq << Set.EqInter.of.Mem.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.apply(Algebra.Any.limits.separate, simplify=None)

    Eq << Eq[-1].this.apply(Algebra.Any.Is.Or.doit.setlimit)





if __name__ == '__main__':
    run()
# created on 2021-02-03
# updated on 2023-11-17
