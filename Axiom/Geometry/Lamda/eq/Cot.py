from util import *


@apply
def apply(self):
    x, *limits = self.of(Lamda[Cot])
    return Equal(self, Cot(Lamda(x, *limits).simplify()), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(n,))
    Eq << apply(Lamda[j:n](Cot(a[j])))

    _j = Symbol('j', domain=Range(n))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[0], _j)


if __name__ == '__main__':
    run()
# created on 2023-06-08
