from util import *


@apply
def apply(contains_j, contains_i):
    j, Sj = contains_j.of(Contains)
    i, Si = contains_i.of(Contains)

    if not Sj._has(i):
        i, Si, j, Sj = j, Sj, i, Si
    assert Sj._has(i)

    a_d, n_d = Si.of(Range)
    i_d, n = Sj.of(Range)

    d = i - i_d

    a = a_d - d
    assert n_d == n + d

    return Contains(i, Range(a + d, d + j + 1)), Contains(j, Range(a, n))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(Contains(j, Range(i - d + 1, n)), Contains(i, Range(a + d, d + n - 1)))

    Eq << sets.contains.imply.contains.sub.apply(Eq[1], d)

    Eq << sets.contains.given.contains.sub.apply(Eq[2], d)

    Eq <<= sets.contains.given.et.split.range.apply(Eq[-1]), sets.contains.given.et.split.range.apply(Eq[3])

    Eq <<= sets.contains.imply.et.split.range.apply(Eq[0]), sets.contains.imply.et.split.range.apply(Eq[4])

    Eq << algebra.ge.imply.gt.transit.apply(Eq[-2])

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[-1], Eq[6])

    Eq << Eq[-2].reversed

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()

from . import left_close