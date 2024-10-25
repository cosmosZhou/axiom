from util import *



@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Abs)
    return LessEqual(x, a), GreaterEqual(x, -a)


@prove
def prove(Eq):
    from axiom import algebra
    x, a = Symbol(integer=True, given=True)

    Eq << apply(abs(x) <= a)

    Eq << algebra.le.ge.then.le.abs.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-06-27
