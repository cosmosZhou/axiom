from util import *


@apply
def apply(eq_R, eq_D, j):
    r, R = eq_R.of(Equal[Expr * OneMatrix])
    (i, limit_i), D = eq_D.of(Equal[OneMatrix * Lamda])
    S[i], S[0], k = limit_i
    return Equal(Sum[j:i, i:k](log(sigmoid(r[j] - r[i]))) / Binomial(k, 2), ReducedSum(
        ReducedSum(log(sigmoid((R - R.T) * sign(D.T - D))))) / (k * (k - 1)) + log(2) / (k - 1))



@prove
def prove(Eq):
    from axiom import discrete, algebra, keras

    k = Symbol(domain=Range(2, oo))
    # k is the size of the rank list
    r = Symbol(real=True, shape=(k,))
    R, D = Symbol(real=True, shape=(k, k))
    i, j = Symbol(integer=True)
    Eq << apply(
    # the following is equivalent to r.unsqueeze(-2) in pytorch
        Equal(R, r * OneMatrix(k, k)),
    # the following is equivalent to torch.arange(k).unsqueeze(0) in pytorch
        Equal(D, Lamda[i:k](i) * OneMatrix(k, k)), j)

    A = Symbol(Eq[-1].find(Mul[Sign]))
    Eq.A_def = A.this.definition

    Eq << Eq[-1].subs(Eq.A_def.reversed)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.div.binom)

    Eq << Eq[-1] * (k * (k - 1))

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add, -1)

    Eq << Eq.A_def.this.rhs.subs(Eq[0], Eq[1])

    Eq << Eq[-1].this.rhs.find(Add[Mul]).apply(algebra.sub.transpose.to.lamda, i, j, simplify=None)

    Eq << Eq[-1].this.rhs.find(Add[Mul]).apply(algebra.sub.transpose.to.lamda, i, j, simplify=None)

    Eq << Eq[-1].this.find(Sign).apply(algebra.sign.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda * Lamda).apply(algebra.mul.lamda.to.lamda)

    Eq << algebra.eq.then.eq.transpose.apply(Eq.A_def)

    Eq << Eq[-1].this.find(Sign).apply(algebra.sign.to.neg.sign)

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq.A_def, Eq[-1])

    Eq << keras.eq.then.eq.sigmoid.apply(Eq[-1])

    Eq << algebra.eq.then.eq.log.apply(Eq[-1])

    Eq << algebra.eq_transpose.then.eq.sum.apply(Eq[-1], i, j)

    Eq << Eq.A_def[i, i]

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(sigmoid).defun()

    Eq << Eq.A_def[i, j].this.rhs.subs(Eq[0][i, j], Eq[1][i, j], Eq[0][j, i], Eq[1][j, i])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum)().find(sign).simplify()

    Eq << algebra.eq.then.eq.transport.apply(Eq[-1], rhs=0).reversed

    # reference:
    # https://arxiv.org/pdf/2203.02155.pdf#page=8




if __name__ == '__main__':
    run()
# created on 2023-05-24
# updated on 2023-08-28
