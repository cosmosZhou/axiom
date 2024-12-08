from util import *


@apply
def apply(gt):
    A, B = gt.of(Arg + Arg > Pi)
    return Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1)


@prove
def prove(Eq):
    from Axiom import Sets

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) > S.Pi)

    Eq <<= Sets.Arg.el.Lopen_.NegPi.Pi.apply(A), Sets.Arg.el.Lopen_.NegPi.Pi.apply(B)

    Eq << Sets.In.In.to.In.Add.Interval.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[-1], S.Pi * 2)

    Eq << Eq[0] / (S.Pi * 2)

    Eq << Sets.Gt.In_Interval.to.In.Interval.Intersect.apply(Eq[-1], Eq[-2])

    Eq << Sets.In.to.In.Sub.apply(Eq[-1], S.One / 2)
    Eq << Sets.In_Interval.to.In_Range.Ceiling.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-10-27
