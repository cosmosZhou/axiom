from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    return Greater(a, x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x < a)

    Eq << algebra.iff.of.et.infer.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2020-01-10
