from util import *


@apply
def apply(given, indices):
    eqs = given.of(Unequal[Probability[And], 0])
    if eqs[-1].is_Tuple:
        eqs, *weights = eqs
    else:
        weights = ()

    args = []
    for eq, t in zip(eqs, indices):
        x, S[x.var] = eq.of(Equal)
        args.append(x[t])

    return Unequal(Probability(*args, *weights), 0)


@prove
def prove(Eq):
    from axiom import algebra, stats

    n = Symbol(domain=Range(2, oo))
    x, y = Symbol(real=True, shape=(n,), random=True)
    t = Symbol(domain=Range(1, n))
    Eq << apply(Unequal(Probability(x, y), 0), [slice(0, t), slice(0, t)])

    Eq << Eq[0].this.lhs.arg.args[-1].apply(algebra.eq.imply.et.eq.split, t)

    Eq << Eq[-1].this.lhs.arg.args[0].apply(algebra.eq.imply.et.eq.split, t)

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[-1])

    Eq << stats.ne_zero.imply.ne_zero.delete.apply(Eq[-2], index=1)





if __name__ == '__main__':
    run()
# created on 2020-12-12
# updated on 2023-03-26
