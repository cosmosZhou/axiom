from util import *



@apply
def apply(self):
    expr = self.of(Unequal[0])
    n, two = expr.of(Mod)
    assert two == 2
    return Equal(expr, 1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ne_zero.then.is_odd)

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.of.is_odd)

if __name__ == '__main__':
    run()
# created on 2020-01-27
