from util import *


@apply
def apply(is_zero, n=None):
    x = is_zero.of(Equal[Cos, 0])
    return Equal(x, S.Pi / 2 + S.Pi * Floor(x / S.Pi))


@prove
def prove(Eq):
    from Axiom import Set, Geometry, Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(cos(x), 0))

    Eq << Set.Sub_Mul_FloorDiv.In.Range.apply(x, S.Pi)

    Eq << Geometry.Cos.eq.Zero.of.Cos.eq.Zero.apply(Eq[0], -Floor(x / S.Pi))

    Eq << Geometry.Eq.of.Cos.eq.Zero.Mem.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.apply(Algebra.Eq.transport)

    # https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-24

from . import Mem
