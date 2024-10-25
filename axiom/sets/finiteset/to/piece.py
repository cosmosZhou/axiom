from util import *


@apply
def apply(self):
    ec = self.of(FiniteSet[Piecewise])
    return Equal(self, Piecewise(*((e.set, c) for e, c in ec)))


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(integer=True)
    Eq << apply(FiniteSet(Piecewise((a, b > 0), (a + 2, True))))

    Eq << algebra.cond_piece.of.et.infer.apply(Eq[0])

    Eq << algebra.infer.of.infer.subs.bool.apply(Eq[-2])

    Eq << algebra.infer.of.infer.subs.bool.apply(Eq[-1], invert=True)


if __name__ == '__main__':
    run()
# created on 2023-11-12
