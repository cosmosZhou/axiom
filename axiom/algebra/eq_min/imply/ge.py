from util import *


@apply
def apply(given, index=0):
    args, M = given.of(Equal[Min])
    return GreaterEqual(args[index], M)


@prove
def prove(Eq):
    from axiom import algebra

    M, x = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Equal(M, Min(f(x), g(x))))

    
    Eq << algebra.eq_min.imply.le.apply(Eq[0])
    Eq << Eq[-1].reversed
    


if __name__ == '__main__':
    run()
# created on 2023-04-23
