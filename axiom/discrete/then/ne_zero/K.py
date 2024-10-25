from util import *


from axiom.discrete.K.to.add.definition import K


@apply
def apply(x):
    assert x > 0
    return Unequal(K(x), 0)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(real=True, positive=True, shape=(oo,))
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(x[:n])

    Eq << discrete.then.gt_zero.K.apply(x[:n])

    Eq << algebra.gt_zero.then.ne_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-05
