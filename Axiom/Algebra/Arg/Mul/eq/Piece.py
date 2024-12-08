from util import *


@apply
def apply(self):
    args = self.of(Arg[Mul])
    s = Add(*(Arg(arg) for arg in args))
    return Equal(self, Piecewise((0, Or(*(Equal(arg, 0) for arg in args))), (s - Ceiling(s / (2 * S.Pi) - S.One / 2) * 2 * S.Pi, True)))


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(complex=True, given=True)
    Eq << apply(Arg(x * y))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=Eq[0].find(Or))

    Eq << Algebra.Imply.of.Imply.subs.Bool.apply(Eq[-2])

    Eq << Eq[-1].this.lhs.apply(Algebra.Or.to.Eq_0)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Algebra.Imply.of.Imply.subs.Bool.apply(Eq[2], invert=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne_0.Ne_0.to.Arg.eq.Add)


if __name__ == '__main__':
    run()

# created on 2018-10-26
