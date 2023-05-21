from util import *

def extract(p_polynomial, x, y):
    assert x.shape == y.shape
    n, = p_polynomial.shape

    if p_polynomial.is_Lamda:
        (b, e), (k, *_) = p_polynomial.of(Lamda[Pow])
    else:
        b, (e, (k, *_)) = p_polynomial.of(Pow[Lamda])

    assert not b.has(k)
    assert not b.is_given
    assert not x._has(b) and not y._has(b)
    assert e.as_poly(k).degree() == 1
    return x, y

@apply
def apply(given):
    (p, x), (S[p], y) = given.of(Equal[MatMul[2]])
    return Equal(*extract(p, x, y))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    p = Symbol(complex=True, zero=False)
    n, k = Symbol(domain=Range(1, oo))
    print(n.dtype)
    x, y = Symbol(shape=(n,), complex=True, given=True)
    Eq << apply(Equal(Lamda[k:n](p ** k) @ x, Lamda[k:n](p ** k) @ y))

    i = Symbol(domain=Range(1, n + 1))
    Eq << Eq[0].subs(p, i)

    Eq << algebra.cond.imply.all.apply(Eq[-1], i)

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].this.rhs.apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].T

    Eq << Eq[-1].this.find(Add[Lamda]).apply(algebra.add.to.lamda).this.find(Pow[Lamda]).apply(algebra.pow.to.lamda, simplify=None)

    Eq.statement = Eq[-1].this.find(Add[Lamda]).apply(algebra.add.to.lamda).this.find(Pow[Lamda]).apply(algebra.pow.to.lamda, simplify=None)

    i, k = Eq.statement.lhs.args[1].variables
    j = Symbol(integer=True)
    Eq << discrete.det_lamda.to.prod.vandermonde.st.linear.apply(Det(Lamda[j:n, i:n]((j + 1) ** i)))

    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    j, i = Eq[-1].lhs.arg.variables
    Eq << Eq[-1].this.lhs.arg.limits_subs(i, k)

    Eq << Eq[-1].this.find(Add[~Lamda]).limits_subs(j, i)

    Eq << Eq[-1].this.find(Add[Lamda]).apply(algebra.add.to.lamda).this.find(Pow[Lamda]).apply(algebra.pow.to.lamda, simplify=None)

    Eq << discrete.ne_zero.eq.imply.eq.matmul.apply(Eq[-1], Eq.statement)





if __name__ == '__main__':
    run()
# created on 2020-08-21
# updated on 2023-04-08
