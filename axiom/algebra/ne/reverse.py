from util import *


@apply
def apply(ne):
    a, b = ne.of(Unequal)
    return Unequal(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    b, a = Symbol(real=True, given=True)
    Eq << apply(Unequal(a, b))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])




if __name__ == '__main__':
    run()
# created on 2020-02-07
