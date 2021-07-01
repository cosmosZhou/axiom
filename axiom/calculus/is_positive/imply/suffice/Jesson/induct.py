from util import *


@apply
def apply(is_positive, x=None, w=None, i=None, n=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2

    domain = x_.domain
    assert domain.left_open and domain.right_open
    if x is None:
        x = Symbol.x(shape=(oo,), domain=domain)

    if w is None:
        w = Symbol.w(shape=(oo,), real=True)

    if i is None:
        i = Symbol.i(integer=True)

    if n is None:
        n = Symbol.n(integer=True, positive=True)

    assert x.domain_assumed == domain
    return Suffice(Equal(Sum[i:n](w[i]), 1) & All[i:n](w[i] >= 0), GreaterEqual(Sum[i:n](w[i] * fx._subs(x_, x[i])), fx._subs(x_, Sum[i:n](w[i] * x[i]))))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    n = Symbol.n(integer=True, positive=True, given=False)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    x = Symbol.x(domain=domain)
    w = Symbol.w(shape=(oo,), real=True)
    f = Function.f(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0, w=w, n=n)

    Eq.initial = Eq[1].subs(n, 1)

    Eq << Eq.initial.this.lhs.apply(algebra.cond.cond.imply.et, algebra.eq.cond.imply.cond.subs)

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.this.rhs.find(Sum).apply(algebra.sum.to.add.pop_back)

    Eq << Eq[-1].this.find(f[~Sum]).apply(algebra.sum.to.add.pop_back)

    Eq.lt, Eq.ge = algebra.cond.given.suffice.split.apply(Eq[-1], cond=w[n] < 1)

    Eq << Eq.ge.this.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.lhs.apply(algebra.eq_sum.ge.all_is_nonnegative.imply.eq.all_is_zero.squeeze)

    Eq << algebra.suffice_et.given.suffice.subs.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.et.imply.cond, index=1)

    i = Eq[-1].lhs.variable
    fxi = Eq[-1].rhs.find(Sum, f)
    Eq << Eq[-1].lhs.this.apply(algebra.all_is_zero.imply.sum_is_zero.mul, Lamda[i:n](fxi))

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.suffice.given.suffice.split.et.apply(Eq[-1])

    x = fxi.arg.base
    Eq << Eq[-1].lhs.this.apply(algebra.all_is_zero.imply.sum_is_zero.mul, x)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << Eq.lt.this.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.split, cond={n})

    Eq << Eq[-1].this.find(Equal) - w[n]

    Eq << Eq[-1].this.find(Less) - w[n]

    Eq << Eq[-1].this.apply(algebra.suffice.fold, index=1)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.cond.imply.et, algebra.is_positive.eq.imply.eq.div, simplify=None)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.all.imply.et.split, cond={n})

    Eq << Eq[-1].this.apply(algebra.suffice.fold)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.fold, index=slice(0, 2))

    Eq << Eq[-1].this.find(And).apply(algebra.cond.all.imply.all_et, simplify=None)

    Eq << Eq[-1].this.find(And).apply(algebra.cond.cond.imply.et, algebra.is_positive.ge.imply.ge.div)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.flatten)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.fold)

    Eq << Eq[-1].this.apply(algebra.suffice.flatten)

    w_ = Symbol.w(Lamda[i:n](w[i] / (1 - w[n])))
    Eq << w_[i].this.definition * (1 - w[n])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Add[~Sum]).apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.find(Add[~Sum]).apply(algebra.sum.to.mul)

    Eq.induct1 = Eq[-1].this.lhs.apply(sets.lt.ge.imply.contains.interval)

    Eq << algebra.cond.imply.cond.subs.apply(Eq[1], w[:n], w_)

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.find(~Sum >= f).simplify()

    Eq << Eq[-1].this.find(f[~Sum]).simplify()

    Eq << algebra.cond.imply.suffice.apply(Eq[-1], cond=Eq.induct1.lhs)

    Eq << Eq[-1].this.apply(algebra.suffice_suffice.imply.suffice_suffice.et)

    Eq <<  Eq[-1].this.find(And[~Contains]).apply(sets.contains.imply.lt.split.interval)

    Eq << Eq[-1].this.find(And[Less]).apply(algebra.lt.ge.imply.ge.mul)

    Eq.hypothesis = Eq[-1].this.find(GreaterEqual[Mul]) + w[n] * f(x[n])

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=Eq.induct1.lhs)

    Eq << Eq[-1].this.find(Greater).forall((Eq[-1].find(Derivative).variable,))

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Contains(x[n], domain, plausible=True)

    Eq << algebra.cond.imply.suffice.apply(Eq[-1], cond=Eq[-2].lhs)

    Eq <<= Eq[-3] & Eq[-1]

    Eq.suffices = Eq[-1].this.rhs.apply(algebra.cond.imply.suffice, cond=Eq.induct1.rhs.lhs)

    Eq << Contains(x[i], domain, plausible=True)

    Eq << algebra.cond.imply.suffice.apply(Eq[-1], cond=Eq.induct1.rhs.lhs)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1], index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.cond.all.imply.all_et, simplify=None)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1], index=1)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[-1].this.rhs.apply(sets.eq_sum.all.imply.contains.mean)

    Eq << algebra.cond.imply.suffice.apply(Eq[-1], cond=Eq.suffices.lhs)

    Eq <<= Eq.suffices & Eq[-1]

    Eq << Eq[-1].this.rhs.rhs.apply(calculus.contains.contains.contains.all_is_positive.imply.ge.Jesson)

    Eq << Eq[-1].this.find(Sum[Mul]).simplify()

    Eq << Eq[-1].this.find(Sum[Mul, Tuple[0]]).simplify()

    Eq <<= Eq.hypothesis & Eq[-1]

    Eq << Eq[-1].this.find(GreaterEqual & GreaterEqual).apply(algebra.ge.ge.imply.ge.transit)

    Eq << Suffice(Eq[1], Eq.induct, plausible=True)
    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()