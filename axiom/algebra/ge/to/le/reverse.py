from util import *


@apply
def apply(ge):
    x, a = ge.of(GreaterEqual)
    return LessEqual(a, x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x >= a)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2019-06-05
