from util import *


@apply
def apply(is_positive, x=None, w=None, i=None, n=None):
    fx, (x_, S[2]) = is_positive.of(Derivative > 0)

    domain = x_.domain
    assert domain.is_open
    if x is None:
        x = Symbol(shape=(oo,), domain=domain)

    if w is None:
        w = Symbol(shape=(oo,), real=True)

    if i is None:
        i = Symbol(integer=True)

    if n is None:
        n = Symbol(integer=True, positive=True)

    assert x.domain_assumed == domain
    return Imply(Equal(Sum[i:n](w[i]), 1) & All[i:n](w[i] >= 0), GreaterEqual(Sum[i:n](w[i] * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](w[i] * x[i]))))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    n = Symbol(integer=True, positive=True, given=False)
    a, b = Symbol(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    x = Symbol(domain=domain)
    w = Symbol(shape=(oo,), real=True)
    f = Function(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0, w=w, n=n)

    Eq.initial = Eq[1].subs(n, 1)

    Eq << Eq.initial.this.lhs.apply(Algebra.Eq.Cond.to.Cond.subs, ret=0)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(f[~Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq.lt, Eq.ge = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq_Sum.Ge.All_Ge_0.to.Eq.All_Eq_0.squeeze)

    Eq << Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.And.to.Cond, index=1)

    i = Eq[-1].lhs.variable
    fxi = Eq[-1].rhs.find(Sum, f)
    Eq << Eq[-1].lhs.this.apply(Algebra.All_Eq_0.to.Eq_.Sum.Zero.Mul, Lamda[i:n](fxi))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Algebra.Imply.of.And.Imply.apply(Eq[-1])

    x = fxi.arg.base
    Eq << Eq[-1].lhs.this.apply(Algebra.All_Eq_0.to.Eq_.Sum.Zero.Mul, x)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.of.And.subs)

    Eq << Eq.lt.this.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.split, cond={n})

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.find(Less) - w[n]

    Eq << Eq[-1].this.apply(Algebra.Imply.fold, index=2)

    Eq << Eq[-1].this.find(And).apply(Algebra.Gt_0.Eq.to.Eq.Div, simplify=None, ret=1)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Algebra.Mul.eq.Sum)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.to.And.All.split, cond={n})

    Eq << Eq[-1].this.apply(Algebra.Imply.fold)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.fold, index=slice(1, None))

    Eq << Eq[-1].this.find(And).apply(Algebra.Cond.All.to.All.And, simplify=None)

    Eq << Eq[-1].this.find(And).apply(Algebra.Gt_0.Ge.to.Ge.Div, ret=0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.flatten)

    Eq << Eq[-1].this.rhs.apply(Algebra.Imply.fold, 1)

    Eq << Eq[-1].this.apply(Algebra.Imply.flatten)

    w_ = Symbol('w', Lamda[i:n](w[i] / (1 - w[n])))
    Eq << w_[i].this.definition * (1 - w[n])

    Eq << Eq[-1].reversed

    Eq << Algebra.Cond.of.And.subs.apply(Eq[-3], *Eq[-1].args, simplify=None)

    Eq << Eq[-1].this.find(Equal & ~GreaterEqual).apply(Algebra.Cond.to.All.domain_defined, wrt=i)

    Eq.induct1 = Eq[-1].this.lhs.apply(Sets.Lt.Ge.to.In.Interval)

    Eq << Algebra.Cond.to.Cond.subs.apply(Eq[1], w[:n], w_)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.find(~Sum >= f).simplify()

    Eq << Eq[-1].this.find(f[~Sum]).simplify()

    Eq << Algebra.Cond.to.Imply.apply(Eq[-1], cond=Eq.induct1.lhs)

    Eq << Eq[-1].this.apply(Algebra.Imply_Imply.equ.Imply_Imply.And)

    Eq <<  Eq[-1].this.find(And[~Element]).apply(Sets.In_Interval.to.Lt)

    Eq << Eq[-1].this.find(And[Less]).apply(Algebra.Lt.Ge.to.Ge.Mul)

    Eq.hypothesis = Eq[-1].this.find(GreaterEqual[Mul]) + w[n] * f(x[n])

    Eq << Algebra.Cond.to.Imply.apply(Eq[0], cond=Eq.induct1.lhs)

    Eq << Eq[-1].this.find(Greater).apply(Algebra.Cond.to.All, Eq[-1].find(Derivative).variable)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Element(x[n], domain, plausible=True)

    Eq << Algebra.Cond.to.Imply.apply(Eq[-1], cond=Eq[-2].lhs)

    Eq <<= Eq[-3] & Eq[-1]

    Eq.suffices = Eq[-1].this.rhs.apply(Algebra.Cond.to.Imply, cond=Eq.induct1.rhs.lhs)

    Eq << Element(x[i], domain, plausible=True)

    Eq << Algebra.Cond.to.Imply.apply(Eq[-1], cond=Eq.induct1.rhs.lhs)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1], index=1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Cond.All.to.All.And, simplify=None)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1], index=0)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.limits.domain_defined)

    Eq << Eq[-1].this.rhs.apply(Sets.Eq_Sum.All.to.In.mean)

    Eq << Algebra.Cond.to.Imply.apply(Eq[-1], cond=Eq.suffices.lhs)

    Eq <<= Eq.suffices & Eq[-1]

    Eq << Eq[-1].this.rhs.rhs.apply(Calculus.In.In.In.All_Gt_0.to.Ge.Jesson)

    Eq << Eq[-1].this.find(Sum[Mul]).simplify()

    Eq << Eq[-1].this.find(Sum[Mul, Tuple[0]]).simplify()

    Eq <<= Eq.hypothesis & Eq[-1]

    Eq << Eq[-1].this.find(GreaterEqual & GreaterEqual).apply(Algebra.Ge.Ge.to.Ge.trans)

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Algebra.Cond.Imply.to.Cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)





if __name__ == '__main__':
    run()
# created on 2020-06-01
# updated on 2023-08-26
