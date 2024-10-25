from util import *


@apply
def apply(is_nonzero_x, is_nonzero_y):
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    return Unequal(x / y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(complex=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))

    Eq << algebra.ne_zero.then.ne_zero.div.apply(Eq[1])


    Eq << algebra.ne_zero.ne_zero.then.ne_zero.mul.apply(Eq[-1], Eq[0])



if __name__ == '__main__':
    run()
# created on 2023-03-22
