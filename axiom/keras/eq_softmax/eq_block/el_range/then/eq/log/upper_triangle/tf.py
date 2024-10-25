from util import *


@apply
def apply(eq_z, eq_z_quote, el):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (n, u)))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z_quote = \
    eq_z_quote.of(Equal[
        BlockMatrix[
            Lamda[Sliced[Indexed, Tuple[Add[Min]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * OneMatrix],
                Tuple[Min - 1]]] - Lamda[OneMatrix * logsumexp]])

    (S[A], (([S[0]], [S[u - 1]]), S[oo])), z = eq_z.of(Equal[Softmax[Add[Mul[BandPart[OneMatrix] - 1]]]])

    assert n >= 2 and u >= 2

    (h, S[i]), (S[0], (S[u], S[n - i])) = el.of(Element[Indexed, Range[Min]])

    return Equal(log(z[i, h[i] + i]), z_quote[i, h[i]])


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    n, u = Symbol(domain=Range(2, oo))
    h = Symbol(integer=True, shape=(n,))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, n), extended_real=True)
    z_quote = Symbol(shape=(n, Min(u, n)), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(
        Equal(z, softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo)),
        Equal(z_quote, BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1)))) - Lamda[i:n](OneMatrix(Min(u, n)) * logsumexp(A[i, i:Min(n, i + u)]))),
        Element(h[i], Range(Min(n - i, u))))

    Eq << keras.eq_block.then.eq.softmax.upper_triangle.st.logsumexp.tf.apply(Eq[1])

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[0], Eq[-1])

    i = Eq[2].lhs.index
    Eq << Eq[-1][i]

    Eq.eq = Eq[-1][i + h[i]]

    Eq.ge_zero, Eq.lt_min = sets.el_range.then.et.apply(Eq[2])

    Eq << Eq.lt_min.this.find(Add).apply(algebra.expr.to.piece, upper=n)

    Eq << Eq[-1].this(i).find(GreaterEqual).simplify()

    Eq.lt = algebra.lt.then.lt.relax.apply(Eq[-1], upper=Min(n, u))

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq.lt, Eq.eq)

    Eq << Eq[-1].this.find(Less) - i

    Eq << algebra.cond.cond.then.cond.subs.apply(Eq.ge_zero, Eq[-1], invert=True)

    Eq << algebra.eq.then.eq.log.apply(Eq[-1])

    Eq.loss = -algebra.eq.then.eq.sum.apply(Eq[3] * (1 + log(1 + h[i] / 2)), (i, 0, n))





if __name__ == '__main__':
    run()
# created on 2022-01-05
# updated on 2023-05-20
