from util import *


@apply(given=None)
def apply(lt):
    x, a = lt.of(Less)
    return Equivalent(lt, Greater(a, x), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x < a)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2020-01-10
