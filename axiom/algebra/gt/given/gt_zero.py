from util import *


@apply
def apply(given):
    x, y = given.of(Greater)
    return Greater(x - y, ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(x > y)

    Eq << Eq[0] - y

    


if __name__ == '__main__':
    run()
# created on 2019-06-12
# updated on 2023-03-25
