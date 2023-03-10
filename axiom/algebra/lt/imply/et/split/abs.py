from util import *



@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    return Less(x, a), Greater(x, -a)


@prove
def prove(Eq):
    from axiom import algebra
    x, a = Symbol(integer=True, given=True)

    Eq << apply(abs(x) < a)

    Eq << algebra.lt.imply.lt.split.abs.apply(Eq[0])

    Eq << -algebra.lt.imply.lt.split.abs.apply(Eq[0], negate=True)


if __name__ == '__main__':
    run()
# created on 2019-12-28
