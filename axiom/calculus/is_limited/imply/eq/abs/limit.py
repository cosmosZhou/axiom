from util import *


@apply
def apply(is_limited):
    from axiom.calculus.is_limited.imply.any.all.limit_definition import of_limited
    fx, *limits = of_limited(is_limited, real=True)

    return Equal(Limit(abs(fx), *limits), abs(is_limited.lhs))


@prove
def prove(Eq):
    from axiom import sets, algebra, calculus

    x, x0 = Symbol(real=True)
    g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](g(x)), Reals))

    Eq << sets.el_interval.imply.ou.apply(Eq[0], 0)

    Eq << Eq[-1].this.args[1].apply(sets.el_interval.imply.ou, 0, left_open=True, simplify=None)

    Eq << Eq[-1].this.find(Element[FiniteSet]).apply(sets.el_finiteset.imply.eq, simplify=None)

    Eq << algebra.cond.given.et.infer.apply(Eq[1], cond=Eq[-1], simplify=None)

    Eq << algebra.infer_ou.given.et.infer.apply(Eq[-1], None)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-3])

    Eq << Eq[-1].this.lhs.apply(calculus.is_zero.imply.is_zero.limit.abs)

    Eq <<= Eq[-2].this.lhs.apply(sets.is_negative.imply.eq.abs, ret=0), Eq[-3].this.lhs.apply(sets.is_positive.imply.eq.abs, ret=0)

    Eq <<= algebra.infer_et.given.infer.et.subs.apply(Eq[-2]), algebra.infer_et.given.infer.et.subs.apply(Eq[-1])

    Eq <<= algebra.infer_et.given.infer.delete.apply(Eq[-2], 0), algebra.infer_et.given.infer.delete.apply(Eq[-1], 0)

    Eq << Eq[-2].this.lhs.apply(calculus.is_negative.imply.eq.limit.abs)

    Eq << Eq[-1].this.lhs.apply(calculus.is_positive.imply.eq.limit.abs)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-18
# updated on 2023-05-13
