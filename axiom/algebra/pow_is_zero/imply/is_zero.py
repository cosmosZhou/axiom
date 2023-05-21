from util import *


@apply
def apply(given):
    x, n = given.of(Equal[Expr ** Expr, 0])
    assert n.is_integer and n > 0
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** n, 0))

    Eq.hypothesis = Infer(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.lhs.lhs.apply(algebra.pow.to.mul.split.exponent)
    Eq << Eq[-1].this.lhs.apply(algebra.mul_is_zero.imply.ou.is_zero)
    
    Eq << algebra.infer_ou.given.et.infer.apply(Eq[-1])
    
    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)
    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)
    
    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq.hypothesis)

    
    


if __name__ == '__main__':
    run()
# created on 2018-11-03
# updated on 2023-05-21
