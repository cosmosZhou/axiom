from util import *


@apply
def apply(is_nonzero):
    ceiling = is_nonzero.of(Unequal[0])
    ((A, B), S[S.One / (S.Pi * 2)]), S[S.One  / 2] = ceiling.of(Ceiling[(Arg + Arg) * Expr - Expr])
    return Equal(ceiling, 1) | Equal(ceiling, -1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Unequal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 0))

    Eq <<= sets.then.el.arg.apply(A), sets.then.el.arg.apply(B)

    Eq << sets.el.el.then.el.add.interval.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << sets.el.then.el.div.interval.apply(Eq[-1], S.Pi * 2)

    Eq << sets.el.then.el.sub.apply(Eq[-1], S.One / 2)

    Eq << sets.el_interval.then.el_range.ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.range.to.finiteset)

    Eq << sets.el_finiteset.then.ou.eq.apply(Eq[-1])

    Eq << algebra.cond.ou.then.cond.apply(Eq[0], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-10-24
