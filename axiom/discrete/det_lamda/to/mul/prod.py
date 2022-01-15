from util import *


@apply
def apply(a, b):
    n = a.shape[0]

    i, j = Symbol(integer=True)

    return Equal(Det(Lamda[j:n, i:n](a[Min(i, j)] * b[Max(i, j)])),
                 a[0] * b[n - 1] * Product(a[i] * b[i - 1] - a[i - 1] * b[i], (i, 1, n)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = 5
    a, b = Symbol(shape=(n,), complex=True, zero=False)
    Eq << apply(a, b)

    Eq << Symbol.L(Eq[0].lhs.arg).this.definition

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.matrix)

    Eq << Eq[-1] @ MulMatrix(n, 0, 1 / a[0])

    Eq << Eq[-1] @ MulMatrix(n, n - 1, 1 / b[n - 1])

    Eq << Eq[-1] @ MulMatrix(n, n - 2, 1 / b[n - 2])

    Eq << MulMatrix(n, n - 1, b[n - 2]) @ Eq[-1]

    Eq << Eq[-1].apply(discrete.eq.imply.eq.det)
    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].reversed + Eq[0] / (a[0] * b[n - 1])

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].this.rhs.expand()


if __name__ == '__main__':
    run()
# created on 2020-10-15
