from util import *


@apply
def apply(self):
    args = self.of(Add)
    args =[arg.of(Re) for arg in args]

    return Equal(self, Re(Add(*args), evaluate=False))


@prove
def prove(Eq):
    from axiom import algebra

    z, w = Symbol(complex=True)
    Eq << apply(Re(z) + Re(w))

    Eq << algebra.expr.to.add.complex.apply(w)

    Eq << algebra.expr.to.add.complex.apply(z)

    Eq << Eq[0].subs(*Eq[-2:])

    


if __name__ == '__main__':
    run()
# created on 2023-06-03
