from util import *


@apply
def apply(eq, forall):
    wi, i_limit = eq.of(Equal[Sum, 1])
    (S[wi], (xi, domain)), S[i_limit] = forall.of(All[And[Expr >= 0, Element]])
    i, S[0], n = i_limit

    return Element(Sum[i:n](wi * xi), domain)

@prove
def prove(Eq):
    from axiom import algebra, sets

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    a, b = Symbol(real=True)
    w, x = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(Sum[i:n](w[i]), 1), All[i:n]((w[i] >= 0) & Element(x[i], Interval(a, b))))

    Eq.hypothesis = Infer(Eq[0] & Eq[1], Eq[2], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq << algebra.infer_et.of.infer.et.subs.apply(Eq.initial, index=0)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.find(All).apply(algebra.all_et.then.et.all)

    Eq << Eq[-1].this.find(Element[~Sum]).apply(algebra.sum.to.add.pop)

    Eq.lt, Eq.ge = algebra.cond.of.et.infer.split.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.rhs.apply(algebra.infer.fold, 2, swap=True)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.lhs.apply(algebra.eq_sum.ge.all_ge_zero.then.eq.all_is_zero.squeeze)

    Eq << Eq[-1].this.find(All[Element]).apply(algebra.all.then.cond.subs, i, n)

    Eq << algebra.infer_et.of.infer.et.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(All).apply(algebra.all_is_zero.then.sum_is_zero.mul, x)

    Eq << algebra.infer_et.of.infer.et.subs.apply(Eq[-1], index=1)

    Eq << Eq.lt.this.rhs.apply(algebra.infer.fold)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.find(Equal[~Sum]).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.lhs.apply(algebra.eq.lt.then.eq.div, ret=1)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    Eq << Eq[-1].this.find(All[2]).apply(algebra.all.to.et.split, cond={n})

    Eq << Eq[-1].this.rhs.apply(algebra.infer.fold, 2)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.apply(algebra.infer.fold, slice(1, None))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.then.all.et, simplify=None)

    Eq << Eq[-1].this.lhs.find(And).apply(algebra.lt.ge.then.ge.div, ret=0)

    Eq << Eq[-1].this.apply(algebra.infer.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.fold, slice(0, 2), swap=True)

    Eq << Eq[-1].this.rhs.rhs.lhs.apply(sets.lt.ge.then.el.interval)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.fold, 0, swap=True)

    Eq << Eq[-1].this.find(All & All).apply(algebra.all.all.then.all.et)

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.flatten)

    w_ = Symbol('w', Lamda[i:n](w[i] / (1 - w[n])))
    Eq << (w_[i].this.definition * (1 - w[n])).reversed

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.cond.then.cond.subs.apply(Eq.hypothesis, w[:n], w_)

    Eq << algebra.cond.then.infer.apply(Eq[-1], cond=Eq[-2].rhs.lhs)

    Eq << Eq[-1].this.apply(algebra.infer.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.infer_et.then.infer.et)

    Eq << Eq[-1].this.rhs.rhs.apply(sets.el.el.el.then.el.interval)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.rhs.find(Sum).simplify()

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.cond.infer.then.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[0] & Eq[1], Eq.hypothesis)





if __name__ == '__main__':
    run()
# created on 2020-05-31
# updated on 2023-05-21
