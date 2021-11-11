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

    Eq <<= sets.imply.el.arg.apply(A), sets.imply.el.arg.apply(B)

    Eq << sets.el.el.imply.el.add.interval.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << sets.el.imply.el.div.interval.apply(Eq[-1], S.Pi * 2)

    Eq << Eq[0] / (S.Pi * 2)

    Eq << sets.gt.el.imply.el.intersect.apply(Eq[-1], Eq[-2])

    Eq << sets.el.imply.el.sub.apply(Eq[-1], S.One / 2)
    Eq << sets.el.imply.el.ceiling.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-10-27
# updated on 2018-10-27
