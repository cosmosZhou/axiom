from util import *


@apply
def apply(self, k, axis=0, *, simplify=True):
    f, *limits = self.of(Lamda)

    if axis < 0:
        axis += len(limits)

    index = len(limits) - 1 - axis

    i, S[0], m = limits[index]
    limits_before = limits[:index]
    limits_after = limits[index + 1:]

    if k <= m:
        ...
    else:
        assert k.copy(domain=self.domain_defined(k)) <= m

    former = Lamda(f, *limits_before, (i, 0, k), *limits_after)
    latter = Lamda(f._subs(i, i + k), *limits_before, (i, 0, m - k), *limits_after)
    if simplify:
        former = former.simplify()
        latter = latter.simplify()

    return Equal(self, BlockMatrix[axis]([former, latter]), evaluate=False)

@prove
def prove(Eq):
    from Axiom import Algebra

    i = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(m))
    f = Function(real=True)
    Eq << apply(Lamda[i:m](f(i)), k)

    i = Symbol(domain=Range(m))
    Eq << Algebra.Eq.given.Eq.getitem.apply(Eq[0], i)





if __name__ == '__main__':
    run()
# created on 2019-10-15
# updated on 2021-12-21