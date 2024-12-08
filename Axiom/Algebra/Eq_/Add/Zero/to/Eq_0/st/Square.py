from util import *


@apply
def apply(given, index=0):
    args = []
    for arg in given.of(Equal[Add, 0]):
        arg = arg.of(Expr ** 2)
        assert arg.is_extended_real
        args.append(arg)

    return Equal(args[index], 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Equal(x * x + y * y + z * z, 0))

    Eq << ~Eq[1]

    Eq << Algebra.Ne_0.to.Gt_0.Abs.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Gt_0.Square.apply(Eq[-1])

    Eq << Algebra.Add_.AddSquareS.Mul2.ge.Zero.apply(y)

    Eq << Algebra.Add_.AddSquareS.Mul2.ge.Zero.apply(z)

    Eq << Algebra.Ge_0.Ge_0.to.Ge_0.Add.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Ge_0.Gt_0.to.Gt_0.Add.apply(Eq[-1], Eq[-4])

    Eq << Eq[-1].subs(Eq[0])




if __name__ == '__main__':
    run()
# created on 2018-06-08
# updated on 2022-01-07