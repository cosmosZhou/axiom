from util import *


@apply
def apply(pow):
    args = pow.of(Arg[Mul])
    e = set()
    prod = []
    for arg in args:
        if arg.is_Pow:
            arg, n = arg.args
            
            e.add(n)
            if len(e) > 1:
                return       
            prod.append(arg)
        elif arg == -1:
            prod.append(-1)
        else:
            return
    z = Mul(*prod)
    return Equal(pow, Arg(z) * n - Ceiling(Arg(z) * n / (2 * S.Pi) - S.One / 2) * 2 * S.Pi)


@prove
def prove(Eq):
    from axiom import algebra

    z, y = Symbol(complex=True, given=True)
    n = Symbol(integer=True, given=True, positive=True)
    Eq << apply(Arg(z ** n * y ** n))

    x = Symbol(y * z)
    Eq << x.this.definition

    Eq << algebra.eq.imply.eq.pow.apply(Eq[-1], exp=n)

    Eq << Eq[-1].this.rhs.apply(algebra.pow.to.mul.split.base)

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-3].reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.arg_pow.to.add)


if __name__ == '__main__':
    run()