from util import *


@apply
def apply(self, var=None, *, simplify=True):

    kwargs = {'var': var, 'generator': self}

    A, B = self.of(MatMul)
    if len(A.shape) > 1:
        i_limit = A.generate_int_limit(1, **kwargs)
        i, *_ = i_limit
        if len(B.shape) > 1:

            j_limit = B.generate_int_limit(0, {i}, **kwargs)
            j, *_ = j_limit

            k_limit = MatMul.generate_k_limit(A, B, {i, j}, **kwargs)
            k, *_ = k_limit

            assert i != k and k != j and i != j
            rhs = Lamda(Sum(A[i, k] * B[k, j], k_limit).simplify(), j_limit, i_limit)
            if simplify:
                rhs = rhs.simplify()
        else:
            k_limit = MatMul.generate_k_limit(A, B, {i}, **kwargs)
            k, *_ = k_limit

            assert i != k
            rhs = Lamda(Sum(A[i, k] * B[k], k_limit).simplify(), i_limit)
            if simplify:
                rhs = rhs.simplify()
    else:
        assert len(B.shape) > 1
        j_limit = B.generate_int_limit(0, **kwargs)
        j, *_ = j_limit

        k_limit = MatMul.generate_k_limit(A, B, {j}, **kwargs)
        k, *_ = k_limit

        assert k != j
        rhs = Lamda(Sum(A[k] * B[k, j], k_limit).simplify(), j_limit)
        if simplify:
            rhs = rhs.simplify()

    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    # a = Symbol(shape=(n,), complex=True)
    # B = Symbol(shape=(n, n), complex=True)
    # A = Symbol(shape=(n, n), complex=True)
    # b = Symbol(shape=(n,), complex=True)
    # Eq << apply(A @ b)
    A, B = Symbol(shape=(n, n), complex=True)
    Eq << apply(A @ B)


if __name__ == '__main__':
    run()
# created on 2018-04-02
