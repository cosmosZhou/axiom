from util import *



@apply
def apply(given, negate=False):
    x, M = given.of(Less)
    x = x.of(Abs)
    if negate:
        x = -x
    return Less(x, M)


@prove
def prove(Eq):
    from axiom import algebra
    M, a = Symbol(real=True)

    Eq << apply(Less(abs(a), M), negate=True)

    Eq << algebra.then.le.abs.apply(a, negate=True)

    Eq << algebra.le.lt.then.lt.trans.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-12-27
