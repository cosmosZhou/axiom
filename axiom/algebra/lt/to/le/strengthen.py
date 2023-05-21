from util import *


@apply
def apply(lt):
    x, a = lt.of(Less)
    assert x.is_integer and a.is_integer
    return LessEqual(x + 1, a).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x < a)

    Eq << Eq[-1].this.lhs.apply(algebra.lt.to.ge.strengthen)


if __name__ == '__main__':
    run()
# created on 2022-01-02
