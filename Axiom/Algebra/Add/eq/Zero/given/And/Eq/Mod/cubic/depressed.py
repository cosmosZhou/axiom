from util import *


@apply
def apply(is_zero, x=None, d=0):
    from Axiom.Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.cubic import cubic_coefficient
    fx = is_zero.of(Equal[0])
    S[1], S[0], p, q = cubic_coefficient(fx, x=x)

    delta = 4 * p ** 3 / 27 + q ** 2
    U = sqrt(delta) - q
    V = -sqrt(delta) - q

    A = (sqrt(delta) / 2 - q / 2) ** (S.One / 3)
    B = (-sqrt(delta) / 2 - q / 2) ** (S.One / 3)

    w = -S.One / 2 + S.ImaginaryUnit * sqrt(3) / 2
    arg_p = Ceil(3 * Arg(-p / 3) / (S.Pi * 2) - S.One / 2)
    arg_AB = Piecewise((0, Equal(p * Ceil((Arg(U) + Arg(V)) / (2 * S.Pi) - S.One / 2), 0)), (1, Arg(U) + Arg(V) > S.Pi), (-1, True))

    if d == 0:
        x0 = A + B
    elif d == 1:
        x0 = A * w + B
    elif d == 2:
        x0 = A * ~w + B
    else:
        ...

    return Equal((arg_p - arg_AB) % 3, d), Equal(x, x0)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x, p, q = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 3 + p * x + q, 0), x=x, d=1)

    Eq << Set.Arg.In.IocNegPiPi.apply(-p)

    Eq << Set.MemDiv.of.Mem_Icc.apply(Eq[-1], 2 * S.Pi / 3)

    Eq << Set.MemSub.of.Mem_Icc.apply(Eq[-1], S.One / 2)

    Eq << Set.Mem_Range.Ceil.of.Mem_Icc.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.Range.eq.Finset)

    Eq << Set.Ite.In.Finset.apply(Eq[1].find(Piecewise))

    Eq << Set.Neg.In.IccNegS.of.Mem_Icc.apply(Eq[-1])

    Eq << Set.Mem.Add.Finset.of.Mem.Mem.apply(Eq[-1], Eq[-3])

    Eq.contains = Set.Mem.of.Eq_Mod.Mem.sift.apply(Eq[1], Eq[-1])

    Eq <<= Eq[0].cond.this.apply(Algebra.Add.eq.Zero.given.And.Eq.cubic.depressed, x, 1), Eq[0].cond.this.apply(Algebra.Add.eq.Zero.given.And.Eq.cubic.depressed, x, -2)

    Eq <<= Algebra.Cond.of.Cond.Cond.subs.apply(Eq[2], Eq[-2]) & Algebra.Cond.of.Cond.Cond.subs.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Set.Or_Eq.given.Mem.Finset)
    Eq << Algebra.Cond.of.Cond.Given.apply(Eq.contains, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-11-20
