from util import *

from axiom.keras.eq.eq.imply.eq.kmeans.nonoverlapping import cluster, mean


@apply
def apply(eq_sum, eq_union, x=None):
    ((w, i), [S[i]]), M = eq_sum.of(Equal[Sum[Card[Indexed]]])
    (S[w[i]], [S[i]]), (S[0], S[M]) = eq_union.of(Equal[Cup, Range])

    S[M] = x.shape[0]

    j = Symbol(integer=True)

    k = w.shape[0]
    w_ = Symbol("omega^'", cluster(w, x))

    c = Lamda[i](mean(w[i], x))

    return Equivalent(Element(j, w_[i]) & Element(i, Range(k)),
                      Equal(i, ArgMin[i](Norm(x[j] - c[i]))) & Element(j, Range(M)))


@prove
def prove(Eq):
    from axiom import keras

    M, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    k = Symbol(domain=Range(M))
    x = Symbol(real=True, shape=(M, n))
    w = Symbol(shape=(k,), etype=dtype.integer, empty=False)
    Eq << apply(Equal(Sum[i](Card(w[i])), M), Equal(Cup[i](w[i]), k.domain), x=x)

    Eq << keras.eq.eq.imply.eq.kmeans.nonoverlapping.apply(Eq[0], Eq[1], x=x)

    Eq << keras.eq.eq.imply.iff.kmeans.apply(Eq[-2], Eq[-1], x=x)

    Eq << Eq[-1].this.find(Bool).arg.rhs.base.definition

    Eq << Eq[-1].this.find(Bool).arg.rhs.base.defun()


if __name__ == '__main__':
    run()
# created on 2020-12-25
