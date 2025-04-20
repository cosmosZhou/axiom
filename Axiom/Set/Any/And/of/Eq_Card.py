from util import *


@apply
def apply(given, x=None):
    S, n = given.of(Equal[Card])
    assert n > 0
    i = S.generate_var(integer=True)
    kwargs = S.etype.dict
    if 'shape' in kwargs:
        shape = (oo,) + kwargs['shape']
    else:
        shape = (oo,)
    kwargs.pop('shape', None)
    if x is None:
        x = S.generate_var(shape=shape, **kwargs)
    return Any[x[:n]](Equal(S, Cup[i:n]({x[i]})) & Equal(Card(S), n))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    k, n = Symbol(integer=True, positive=True)
    S = Symbol(etype=dtype.integer[k], given=True)
    Eq << apply(Equal(Card(S), n))

    Eq << Set.Any.Eq.Condset.Eq.of.Eq_Card.apply(Eq[0])

    Eq << Algebra.Any.And.of.Any.limits.unleash.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Logic.Cond.of.Eq.Cond.subs, reverse=True, simplify=None, ret=0)


if __name__ == '__main__':
    run()
# created on 2021-02-02
