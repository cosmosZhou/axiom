from util import *



@apply
def apply(given):
    p, q = given.of(Given)
    return p | q.invert()


@prove
def prove(Eq):
    from Axiom import Algebra, Logic
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Given(x > y, f(x) > g(y)))

    Eq << Eq[0].reversed

    Eq << Eq[-1].apply(Logic.Or.of.ImpNot)


if __name__ == '__main__':
    run()
# created on 2018-09-18
