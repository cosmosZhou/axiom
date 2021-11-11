from util import *


@apply
def apply(given):
    f, limit = given.of(Any)
    x, S = limit
    return Unequal(S, x.emptySet)


@prove
def prove(Eq):
    from axiom import algebra

    S = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)
    Eq << apply(Any[e:S](f(e) > 0))

    Eq << Any[e:S](Element(e, S) & Eq[0].expr, plausible=True)

    Eq << Eq[-1].simplify()

    Eq << algebra.any_et.imply.et.any.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-01-16
# updated on 2021-01-16
