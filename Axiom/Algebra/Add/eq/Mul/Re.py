from util import *


@apply
def apply(self):
    x, y = self.of(Add)
    if y == ~x:
        ...
    elif len(x.shape) <= 1:
        assert y.T == ~x
    else:
        return

    return Equal(self, 2 * Re(x, evaluate=False))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(complex=True)
    Eq << apply(x + ~x)

    Eq << Algebra.Expr.eq.AddRe_MulIIm.apply(x)

    Eq << Algebra.Expr.eq.AddRe_MulIIm.apply(~x)

    Eq << Eq[-1] + Eq[-2]




if __name__ == '__main__':
    run()
# created on 2023-05-25
# updated on 2023-06-23
