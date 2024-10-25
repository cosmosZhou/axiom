from util import *


@apply
def apply(self):
    d, S[d] = self.of(Ceiling[Sign / Expr])
    assert d.is_integer
    return Equal(self, 1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    d = Symbol(integer=True, zero=False, given=True)
    Eq << apply(Ceiling(sign(d) / d))

    Eq << sets.eq_ceiling.of.el.interval.apply(Eq[0])

    Eq << sets.el_interval.of.et.apply(Eq[-1])

    Eq << Eq[-2].this.find(Sign).apply(algebra.sign.to.piece.abs)

    Eq << Eq[-1].this.find(Sign).apply(algebra.sign.to.piece.abs)

    Eq << Eq[-1] * abs(d)

    Eq << ~Eq[-1].reversed

    Eq << algebra.lt.then.le.strengthen.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-05-29
