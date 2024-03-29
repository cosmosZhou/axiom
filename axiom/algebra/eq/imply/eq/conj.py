from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return Equal(~lhs, ~rhs, evaluate=False)


@prove
def prove(Eq):
    x = Symbol(complex=True)
    f, g = Function(complex=True)
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].subs(Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2018-08-18
# updated on 2023-06-22
