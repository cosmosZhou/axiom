from util import *


@apply
def apply(imply):
    lhs, rhs = imply.of(Equal)
    return Equal(exp(lhs), exp(rhs))

@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    f, g = Function(shape=(), real=True)
    Eq << apply(Equal(f(x), g(x)))

    Eq << Eq[1].apply(algebra.eq.then.eq.log)


if __name__ == '__main__':
    run()
# created on 2018-08-05
