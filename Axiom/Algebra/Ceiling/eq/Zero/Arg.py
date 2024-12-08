from util import *


@apply
def apply(self):
    z = self.of(Ceiling)
    (z, coeff), S[S.One / 2] = z.of(Arg * Expr - Expr)
    coeff *= S.Pi * 2
    assert coeff <= 1 and coeff >= -1 or 1 / coeff >= 1 or 1 / coeff <= -1
    return Equal(self, 0)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    z = Symbol(complex=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Ceiling(Arg(z) / (2 * S.Pi) / n - S.One / 2))

    Eq << Sets.Arg.el.Lopen_.NegPi.Pi.apply(z)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[-1], n, simplify=None)

    Eq << Sets.In.to.In.Sub.apply(Eq[-1], S.Pi, simplify=None)

    Eq << Sets.In.to.In.Div.Interval.apply(Eq[-1], S.Pi * 2, simplify=None)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq.contains = Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq.le = LessEqual(-1, Eq.contains.rhs.start, plausible=True)

    Eq << Eq.le * (2 * n)

    Eq.ge = GreaterEqual(0, Eq.contains.rhs.stop, plausible=True)

    Eq << Eq.ge * (2 * n)


    Eq << Sets.Le.Ge.In.to.In.Interval.apply(Eq.le, Eq.ge, Eq.contains)

    Eq << Sets.In.to.Eq_.Ceiling.Zero.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2018-11-05
# updated on 2023-04-17
