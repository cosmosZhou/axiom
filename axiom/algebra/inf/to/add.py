from util import *


@apply
def apply(self):
    expr, *limits = self.of(Inf)
    vars = [x for x, *ab in limits]

    args, const = std.array_split(expr.of(Add), lambda arg : arg.has(*vars))
    assert const

    const = Add(*const)
    expr = Add(*args)

    return Equal(self, const + Inf(expr, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M, h = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Inf[x:m:M](f(x) + h))

    y = Symbol(Eq[0].rhs.args[1])
    Eq << y.this.definition.reversed

    Eq <<= algebra.eq.imply.et.squeeze.apply(Eq[-1]), Eq[0].subs(Eq[-1])

    z = Symbol(real=True)
    Eq <<= algebra.inf_le.imply.all.any.lt.apply(Eq[-3], z), algebra.inf_ge.imply.all.ge.apply(Eq[-2]), algebra.eq.given.et.squeeze.apply(Eq[-1])

    Eq <<= algebra.inf_le.given.all_any_lt.apply(Eq[-2], z), algebra.inf_ge.given.all.ge.apply(Eq[-1])

    Eq << algebra.all.given.all.limits.subs.offset.apply(Eq[-1], h)

    Eq << Eq[-1].this.expr.expr - h


if __name__ == '__main__':
    run()
# created on 2019-08-26
