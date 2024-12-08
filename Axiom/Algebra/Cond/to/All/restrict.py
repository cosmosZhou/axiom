from util import *



@apply
def apply(given, *limits):
    limits = [*limits]
    for i, (x, *ab) in enumerate(limits):
        if not ab:
            if x.domain:
                limits[i] = (x, x.domain)
    return All(given, *limits)


@prove
def prove(Eq):
    from Axiom import Algebra
    S = Symbol(etype=dtype.real)
    e = Symbol(real=True)
    f = Function(shape=(), integer=True)

    Eq << apply(f(e) > 0, (e, S))

    Eq << Eq[0].apply(Algebra.Cond.to.And.All, cond=Element(e, S))

    Eq << Algebra.And.to.And.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-04-10
