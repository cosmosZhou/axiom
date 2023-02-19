from util import *


@apply
def apply(eq):
    (H, (((((Q, i), W, (K, (S[0], S[i]))), (S[i], S[0], (l, n))), ((S[Q[i + Min(l, n) - 1]], S[W], S[K[i:i + Min(l, n) - 1].T]), (S[i], S[0], S[n - Min(l, n) + 1]))), (((S[Q[i]], S[W], (S[K], (S[i], (S[i], (S[n], u))))), (S[i], S[0], S[n + 1 - Min(n, u)])), ((S[Q[i + n + 1 - Min(n, u)]], S[W], S[K[i + n - Min(n, u) + 1:].T]), (S[i], S[0], S[Min(n, u) - 1])))), (((S[Q[i]], S[W], S[K[relu(i - l + 1):Min(n, i + u)].T]), S[H[i]]), (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[1][ZeroMatrix, Expr, ZeroMatrix] + BlockMatrix[1][
            BlockMatrix[
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix,
                        Indexed @ Expr @ Transpose[Sliced]
                    ],
                    Tuple[Min - 1]
                ],
                Lamda[MatMul]
            ],
            BlockMatrix[
                Lamda[MatMul[Transpose[Sliced[Tuple[Add[Min]]]]]],
                Lamda[
                    BlockMatrix[
                        MatMul,
                        NegativeInfinity * OneMatrix
                    ]
                ]
            ]
        ] - Lamda[OneMatrix * logsumexp[MatMul + BlockMatrix[ZeroMatrix, Expr, ZeroMatrix]]]])
    assert n >= 2 and u >= 2 and l >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(Q @ W @ K.T + H * Identity(n) + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                    Lamda[i:Min(l, n) - 1](BlockMatrix(Exp(z[i, Min(l, n) - i - 1:Min(l, n) - 1]), ZeroMatrix(n - i))),
                    Lamda[i:n - Min(l, n) + 1](BlockMatrix(ZeroMatrix(i), Exp(z[i + Min(l, n) - 1, :Min(l, n) - 1]), ZeroMatrix(n - i - Min(l, n) + 1)))
                 ) + BlockMatrix(
                    Lamda[i:n - Min(u, n) + 1](BlockMatrix(ZeroMatrix(i), Exp(z[i, Min(l, n) - 1:]), ZeroMatrix(n - i - Min(u, n)))),
                    Lamda[i:Min(u, n) - 1](BlockMatrix(ZeroMatrix(n - Min(u, n) + i + 1), Exp(z[i + n - Min(u, n) + 1, Min(l, n) - 1:breadth - i - 1])))
                 ))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n, l, u = Symbol(domain=Range(2, oo))
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z, d_z), real=True)
    H = Symbol(shape=(n,), real=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](ZeroMatrix(n, Min(l, n) - 1), H, ZeroMatrix(n, Min(u, n) - 1)) + BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n) - 1](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), Q[i] @ W @ K[:i].T)),
            Lamda[i:n - Min(l, n) + 1](Q[i + Min(l, n) - 1] @ W @ K[i:i + Min(l, n) - 1].T)
        ),
        BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](Q[i] @ W @ K[i:i + Min(u, n)].T),
            Lamda[i:Min(u, n) - 1](BlockMatrix(Q[i + n - Min(u, n) + 1] @ W @ K[n - Min(u, n) + i + 1:].T, -oo * OneMatrix(i + 1)))
        )) - Lamda[i:n](OneMatrix(breadth) * logsumexp((Q[i] @ W @ K[relu(i + 1 - l):Min(n, i + u)].T + BlockMatrix(ZeroMatrix(Min(i, l - 1)), H[i], ZeroMatrix(Min(n - i, u) - 1)))))))

    A = Symbol(Eq[1].find(MatMul))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, n + 1 - Min(u, n)))

    Eq << algebra.all_eq.imply.all_eq.slice.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1])

    Eq << Eq.A_def[i][:i]

    Eq << Eq.A_def[i + Min(l, n) - 1][i:i + Min(l, n) - 1]

    Eq << Eq.A_def[i + n + 1 - Min(u, n)][i + n + 1 - Min(u, n):]

    Eq << Eq.A_def[i][relu(i + 1 - l):Min(n, i + u)]

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed, Eq[-4].reversed, Eq[-5].reversed)

    Eq << keras.eq_block.imply.eq.softmax.biased.st.logsumexp.tf.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_def)





if __name__ == '__main__':
    run()
# created on 2022-01-05
# updated on 2022-03-15
