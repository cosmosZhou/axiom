from util import *


@apply
def apply(given, index=0, invert=False):
    eqs = given.of(And)
    if invert:
        eqs = [*eqs]
        del eqs[index]
        return tuple(eqs)
    else:
        return eqs[index]


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    f, g = Function(real=True)
    b = Symbol(shape=(k,), real=True)
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)))

    Eq << Infer(Eq[0], Eq[1], plausible=True)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])

    


if __name__ == '__main__':
    run()

# created on 2018-01-02
# updated on 2023-05-18
