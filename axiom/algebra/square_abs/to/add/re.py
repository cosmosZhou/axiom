from util import *


def sigmar2(args):
    result = []
    for i in range(1, len(args)):
        for j in range(i):
            result.append(Re(~args[i] * args[j]) * 2)
    return Add(*result)
@apply
def apply(self):
    args = self.of(Abs[Add] ** 2)
    return Equal(self, Add(*(abs(arg) ** 2 for arg in args), sigmar2(args)))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(complex=True)
    Eq << apply(abs(x + y + z) ** 2)

    Eq << Eq[-1].lhs.this.apply(algebra.square_abs.to.mul.conj)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul_conj.to.square.abs)

    Eq << Eq[-1].this.rhs.args[:4:2].apply(algebra.add.to.mul.re)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.mul_conj.to.square.abs)

    Eq << Eq[-1].this.rhs.args[:4:2].apply(algebra.add.to.mul.re)

    Eq << Eq[-1].this.rhs.args[:2].apply(algebra.add.to.mul.re)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul_conj.to.square.abs)

    


if __name__ == '__main__':
    run()
# created on 2023-06-24
