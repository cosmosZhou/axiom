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
    from Axiom import Sets, Algebra

    k = Symbol(integer=True, positive=True)
    s = Symbol(etype=dtype.integer[k], given=True)
    Eq << apply(Card(s) > 0)

    Eq << Sets.Gt.to.In.Range.apply(Eq[0])

    m = Symbol(integer=True, positive=True)
    Eq << Sets.In.to.Any.Eq.apply(Eq[-1], var=m)

    Eq << Eq[-1].this.expr.apply(Sets.Eq_Card.to.Any.And, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Eq.to.Eq.subs, swap=True, reverse=True, simplify=None, ret=1)

    Eq << Algebra.Any_And.to.Any.limits_absorb.apply(Eq[-1], 1)

    Eq << Sets.In.to.Eq.Intersect.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.apply(Algebra.Any.limits.separate, simplify=None)

    Eq << Eq[-1].this.apply(Algebra.Any.equ.Or.doit.setlimit)





if __name__ == '__main__':
    run()
# created on 2021-02-03
# updated on 2023-11-17
