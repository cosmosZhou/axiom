from util import *



@apply
def apply(given):
    x, y = given.of(Less)
    return Greater(y - x, 0)


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << Eq[0] - y

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-06-24
# updated on 2019-06-24