from util import *


@apply
def apply(self):
    assert self.is_OneMatrix
    indices, limits = self.variables_with_limits()

    return Equal(self, Lamda(S.One, *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True)
    Eq << apply(OneMatrix(m, n))

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.of.eq.getitem.apply(Eq[0], i)

    j = Symbol(domain=Range(n))
    Eq << algebra.eq.of.eq.getitem.apply(Eq[-1], j)


if __name__ == '__main__':
    run()
# created on 2023-03-19
