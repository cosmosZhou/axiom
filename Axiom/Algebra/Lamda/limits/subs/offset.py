from util import *


@apply
def apply(self, index=0, offset=None):
    from Axiom.Algebra.Sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Lamda, self, index, offset, simplify=False), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b, i, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Lamda[i:a:b](f(i)), d)

    i = Symbol(domain=Range(b - a))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[0], i)




if __name__ == '__main__':
    run()
# created on 2021-12-29
