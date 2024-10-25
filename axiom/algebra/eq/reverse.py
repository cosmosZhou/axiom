from util import *


@apply
def apply(eq):
    a, b = eq.of(Equal)
    return Equal(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    b, a = Symbol(real=True, given=True)
    Eq << apply(Equal(a, b))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-04-19
