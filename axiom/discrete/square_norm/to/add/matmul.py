from util import *


def sigmar2(args):
    result = []
    for i in range(1, len(args)):
        for j in range(i):
            result.append(Re(~args[i] @ args[j]) * 2)
    return Add(*result)

@apply
def apply(self):
    args = self.of(Norm[Add] ** 2)
    return Equal(self, Add(*(Norm(arg) ** 2 for arg in args), sigmar2(args)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    x, y, z = Symbol(complex=True, shape=(n,))
    Eq << apply(Norm(x + y + z) ** 2)

    Eq << Eq[-1].lhs.this.apply(discrete.square_norm.to.matmul.conj)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.add, deep=True)

    Eq << Eq[-1].this.rhs.args[0].apply(discrete.matmul.to.square.norm)

    Eq << Eq[-1].this.rhs.args[:4:2].apply(algebra.add.to.mul.re)

    Eq << Eq[-1].this.rhs.args[1].apply(discrete.matmul.to.square.norm)

    Eq << Eq[-1].this.rhs.args[:4:2].apply(algebra.add.to.mul.re)

    Eq << Eq[-1].this.rhs.args[:2].apply(algebra.add.to.mul.re)

    Eq << Eq[-1].this.rhs.args[0].apply(discrete.matmul.to.square.norm)

    Eq << Eq[-1].this.find(MatMul).T

    Eq << Eq[-1].this.find(Mul[2]).find(MatMul).T

    Eq << Eq[-1].this.find(MatMul).T


if __name__ == '__main__':
    run()
# created on 2023-06-24
