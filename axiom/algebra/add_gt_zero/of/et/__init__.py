from util import *


@apply
def apply(given, index=-1, swap=False):
    [*args] = given.of(Add > 0)
    first = args[index]
    del args[index]
    if isinstance(index, slice):
        first = Add(*first)
    second = Add(*args)
    if swap:
        return first >= 0, second > 0
    return first > 0, second >= 0



@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    Eq << apply(a + b + c > 0)

    Eq << algebra.ge_zero.gt_zero.then.gt_zero.add.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

from . import gt_zero
# created on 2018-08-12
