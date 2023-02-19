from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = self.of(Sum)
    variables = self.variables

    for _, cond in function.of(Piecewise):
        assert not cond.has(*variables)

    ecs = [(self.func(expr, *limits).simplify(), cond) for expr, cond in function.of(Piecewise)]

    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    x, y = Symbol(integer=True, given=True)
    A, B, C, D = Symbol(etype=dtype.integer, given=True)
    f, h = Function(real=True)
    Eq << apply(Sum[j:D, i:C](Piecewise((f(i, j), Element(x, A) & Element(y, B)), (h(i, j), True))))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[1].apply(algebra.et.given.et.subs.bool, index=slice(0, 2))

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=0, invert=True)

    Eq << algebra.ou.given.et.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-03-10
# updated on 2022-09-20
