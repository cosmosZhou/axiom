from util import *


@apply
def apply(self):
    coeff, arg = self.of(Expr * Im)
    assert coeff.is_super_real

    return Equal(self, Im(arg * coeff, evaluate=False))


@prove
def prove(Eq):
    from axiom import algebra

    c = Symbol(real=True)
    z = Symbol(complex=True)
    Eq << apply(Im(z) * c)

    Eq << algebra.expr.to.add.complex.apply(z)

    Eq << Eq[0].subs(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-06-03
