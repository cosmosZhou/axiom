from util import *


@apply
def apply(self):
    expr, (i,) = self.of(Cup)
    return Equal(self, Cup[i](expr._subs(i, -i)), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[i](f(i)))

    Eq << sets.eq.of.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.then.any_el), Eq[-1].this.rhs.apply(sets.el_cup.of.any_el)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_cup.of.any_el), Eq[-1].this.lhs.apply(sets.el_cup.then.any_el)

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.then.any.limits.negate.oo)

    Eq <<= Eq[-1].this.lhs.apply(algebra.any.then.any.limits.negate.oo)


if __name__ == '__main__':
    run()
# created on 2018-10-05
