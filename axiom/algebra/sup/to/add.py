from util import *


@apply
def apply(self):
    expr, *limits = self.of(Sup)
    vars = [x for x, *ab in limits]
    args, const = std.array_split(expr.of(Add), lambda arg: arg.has(*vars))
    assert const

    const = Add(*const)
    expr = Add(*args)

    return Equal(self, const + Sup(expr, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Sup[x:m:M](f(x) + h))

    y = Symbol(Eq[0].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq <<= algebra.eq.then.et.squeeze.apply(Eq[-1]), Eq[0].subs(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.sup_le.then.all.le.apply(Eq[-3]), algebra.sup_ge.then.all.any.gt.apply(Eq[-2], z), algebra.eq.of.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.sup_le.of.all.le.apply(Eq[-2]), algebra.sup_ge.of.all_any_gt.apply(Eq[-1], z)

    Eq << algebra.all.of.all.limits.subs.offset.apply(Eq[-1], h)

    Eq << Eq[-1].this.expr.expr - h


if __name__ == '__main__':
    run()
# created on 2019-09-09
