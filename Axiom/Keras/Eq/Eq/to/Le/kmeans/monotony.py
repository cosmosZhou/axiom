from util import *


@apply
def apply(eq_sum, eq_union, x=None):
    from Axiom.Keras.Eq.Eq.to.Eq.kmeans.nonoverlapping import cluster, mean

    ((w, i), S[i]), M = eq_sum.of(Equal[Sum[Card[Indexed], Tuple]])
    ((S[w], i), S[i]), (S[0], S[M]) = eq_union.of(Equal[Cup[Indexed, Tuple], Range])

    assert x.shape[0] == M

    w_ = Symbol("omega^'", cluster(w, x))

    j = Symbol(integer=True)

    return LessEqual(Sum[j:w_[i], i](Norm(x[j] - mean(w_[i], x)) ** 2),
                     Sum[j:w[i], i](Norm(x[j] - mean(w[i], x)) ** 2))




@prove(proved=False)
def prove(Eq):
    from Axiom import Keras, Algebra, Sets

    M, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    k = Symbol(domain=Range(M))
    x = Symbol(real=True, shape=(M, n))
    w = Symbol(shape=(k,), etype=dtype.integer, empty=False)
    Eq << apply(Equal(Sum[i](Card(w[i])), M), Equal(Cup[i](w[i]), k.domain), x=x)

    Eq << Keras.Eq.Eq.to.Iff.kmeans.apply(Eq[0], Eq[1], x=x)

    Eq << Algebra.Iff.to.Eq.Sum.collapse.apply(Eq[-1], Eq[3].rhs.expr)

    i_ = Symbol('i', Eq[-1].find(Indexed, Sum))
    Eq << Eq[-1].subs(i_.this.definition.reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.domain_defined.delete)

    Eq.plausible = Eq[3].subs(Eq[-1])

    Eq << Keras.Eq.Eq.to.Iff.kmeans.w_quote.apply(Eq[0], Eq[1], x=x)

    Eq << Algebra.Iff.to.Eq.Sum.collapse.apply(Eq[-1], Eq.plausible.lhs.expr)

    i__ = Symbol("i'", Eq[-1].find(Indexed, ArgMin))
    Eq << Eq[-1].subs(i__.this.definition.reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.domain_defined.delete)

    Eq.plausible = Eq.plausible.subs(Eq[-1])

    Eq << Eq.plausible.this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq.le = Eq[-1].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq.le.find(mean, Indexed).this.definition

    Eq << Eq[-1].this.rhs.definition

    Eq << Sets.Eq_Cup.to.All.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Eq_ArgMin.to.All.Le)

    Eq << Eq[-1].this.expr.apply(Algebra.Le.to.Le.Square)

    Eq << Eq[-1].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq.le.find(mean).this.defun()

    Eq << Eq[-1][i]

    Eq << Eq.le.rhs.find(mean).this.defun()

    Eq << Eq[-1][i]

    Eq << Eq.le.subs(Eq[-1], Eq[-3])

    Eq << Algebra.Le.of.Ge_0.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Sum.Sub)

    Eq << Eq[-1].this.lhs.expr.expand()

    Eq << Algebra.Ge_.Sum.Zero.of.Ge_.Sum.Zero.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-12-26
# updated on 2021-12-27