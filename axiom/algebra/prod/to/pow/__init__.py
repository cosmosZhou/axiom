from util import *


@apply
def apply(self, simplify=True):
    (b, e), *limits = self.of(Product[Pow])
    assert not e.has(*self.variables)
    return Equal(self, Product(b, *limits) ** e)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Function(real=True)
    a = Symbol(real=True)
    Eq << apply(Product[i:n](f(i) ** a))



    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq[0] * f(n) ** a

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.prod.limits.push)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.pow.mul.base)

    Eq << Eq[-1].this.find(Mul[Product]).apply(algebra.mul.to.prod.limits.push)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.then.eq.induct.apply(Eq[-1], n)




if __name__ == '__main__':
    run()
# created on 2023-03-30


from . import sum