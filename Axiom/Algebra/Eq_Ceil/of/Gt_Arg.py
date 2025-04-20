from util import *


@apply
def apply(gt):
    A, B = gt.of(Arg + Arg > Pi)
    return Equal(Ceil((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1)


@prove
def prove(Eq):
    from Axiom import Set

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) > S.Pi)

    Eq <<= Set.Arg.In.IocNegPiPi.apply(A), Set.Arg.In.IocNegPiPi.apply(B)

    Eq << Set.Mem.Add.Icc.of.Mem.Mem.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Set.MemDiv.of.Mem_Icc.apply(Eq[-1], S.Pi * 2)

    Eq << Eq[0] / (S.Pi * 2)

    Eq << Set.Mem.Icc.Inter.of.Gt.Mem_Icc.apply(Eq[-1], Eq[-2])

    Eq << Set.MemSub.of.Mem_Icc.apply(Eq[-1], S.One / 2)
    Eq << Set.Mem_Range.Ceil.of.Mem_Icc.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-10-27
