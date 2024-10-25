from util import *


@apply
def apply(self):
    expr, *limits = self.of(Conjugate[Lamda])
    return Equal(self, Lamda(~expr, *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    h = Function(complex=True)
    Eq << apply(Conjugate(Lamda[i:n](h(i * S.ImaginaryUnit)), evaluate=False))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.of.eq.getitem.apply(Eq[0], i)




if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-24
