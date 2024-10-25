from util import *


@apply
def apply(gt):
    A, B = gt.of(Arg + Arg > Pi)
    return Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1)


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) > S.Pi)

    Eq <<= sets.then.el.arg.apply(A), sets.then.el.arg.apply(B)

    Eq << sets.el.el.then.el.add.interval.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << sets.el.then.el.div.interval.apply(Eq[-1], S.Pi * 2)

    Eq << Eq[0] / (S.Pi * 2)

    Eq << sets.gt.el_interval.then.el.interval.intersect.apply(Eq[-1], Eq[-2])

    Eq << sets.el.then.el.sub.apply(Eq[-1], S.One / 2)
    Eq << sets.el_interval.then.el_range.ceiling.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-10-27
