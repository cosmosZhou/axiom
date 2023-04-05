from util import *


@apply
def apply(self, k, axis=0):
    index_upper = [slice(None, None)] * axis
    index_lower = [slice(None, None)] * axis
    index_upper.append(slice(0, k))
    index_lower.append(slice(k, self.shape[axis]))

    rhs = BlockMatrix[axis](self[tuple(index_upper)], self[tuple(index_lower)], shape=self.shape)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    m = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(oo,))
    i = Symbol(domain=Range(1, m))
    Eq << apply(a[:m], i)

    t = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], t)


if __name__ == '__main__':
    run()
# created on 2023-03-31
