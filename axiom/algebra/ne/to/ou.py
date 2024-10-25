from util import *


@apply
def apply(given):
    x, y = given.of(Unequal)
    assert x.is_real and y.is_real
    return Or(x > y, x < y, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ne.then.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.ne.of.ou)




if __name__ == '__main__':
    run()
# created on 2023-04-19
