from util import *


@apply
def apply(self, simplify=True):
    (expr, *l_limits), *s_limits = self.of(Sum[Lamda])
    return Equal(self, Lamda(Sum(expr, *s_limits), *l_limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    C = Symbol(etype=dtype.integer, given=True)
    f = Function(real=True)
    Eq << apply(Sum[i:C](Lamda[j:n](f(i, j))))

    t = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], t)

    


if __name__ == '__main__':
    run()
# created on 2023-03-18