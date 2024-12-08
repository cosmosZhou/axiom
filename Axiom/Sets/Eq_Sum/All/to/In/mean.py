from util import *


@apply
def apply(eq, forall):
    wi, i_limit = eq.of(Equal[Sum, 1])
    (S[wi], (xi, domain)), S[i_limit] = forall.of(All[And[Expr >= 0, Element]])
    i, S[0], n = i_limit

    return Element(Sum[i:n](wi * xi), domain)

@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    a, b = Symbol(real=True)
    w, x = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(Sum[i:n](w[i]), 1), All[i:n]((w[i] >= 0) & Element(x[i], Interval(a, b))))

    Eq.hypothesis = Imply(Eq[0] & Eq[1], Eq[2], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq << Algebra.Imply_And.of.Imply.And.subs.apply(Eq.initial, index=0)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.find(All).apply(Algebra.All_And.to.And.All)

    Eq << Eq[-1].this.find(Element[~Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq.lt, Eq.ge = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.rhs.apply(Algebra.Imply.fold, 2, swap=True)

    Eq << Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq_Sum.Ge.All_Ge_0.to.Eq.All_Eq_0.squeeze)

    Eq << Eq[-1].this.find(All[Element]).apply(Algebra.All.to.Cond.subs, i, n)

    Eq << Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(Algebra.All_Eq_0.to.Eq_.Sum.Zero.Mul, x)

    Eq << Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1], index=1)

    Eq << Eq.lt.this.rhs.apply(Algebra.Imply.fold)

    Eq << Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.find(Equal[~Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq.Lt.to.Eq.Div, ret=1)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Algebra.Mul.eq.Sum)

    Eq << Eq[-1].this.find(All).apply(Algebra.All.equ.And.split, cond={n})

    Eq << Eq[-1].this.find(All[2]).apply(Algebra.All.equ.And.split, cond={n})

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.fold, 2)

    Eq << Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.apply(Algebra.Imply.fold, slice(1, None))

    Eq << Eq[-1].this.lhs.apply(Algebra.Cond.All.to.All.And, simplify=None)

    Eq << Eq[-1].this.lhs.find(And).apply(Algebra.Lt.Ge.to.Ge.Div, ret=0)

    Eq << Eq[-1].this.apply(Algebra.Imply.swap)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.fold, slice(0, 2), swap=True)

    Eq << Eq[-1].this.rhs.rhs.lhs.apply(Sets.Lt.Ge.to.In.Interval)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.fold, 0, swap=True)

    Eq << Eq[-1].this.find(All & All).apply(Algebra.All.All.to.All.And)

    Eq << Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.flatten)

    w_ = Symbol('w', Lamda[i:n](w[i] / (1 - w[n])))
    Eq << (w_[i].this.definition * (1 - w[n])).reversed

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Cond.to.Cond.subs.apply(Eq.hypothesis, w[:n], w_)

    Eq << Algebra.Cond.to.Imply.apply(Eq[-1], cond=Eq[-2].rhs.lhs)

    Eq << Eq[-1].this.apply(Algebra.Imply.swap)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply_And.to.Imply.And)

    Eq << Eq[-1].this.rhs.rhs.apply(Sets.In.In.In.to.In.Interval)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.rhs.find(Sum).simplify()

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0] & Eq[1], Eq.hypothesis)





if __name__ == '__main__':
    run()
# created on 2020-05-31
# updated on 2023-05-21
