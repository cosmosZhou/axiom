from util import *


@apply
def apply(self):
    expr = self.of(Unequal[1])
    n, two = expr.of(Mod)
    assert two == 2
    return Equal(expr, 0)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    Eq << apply(Unequal(n % 2, 1))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ne_one.imply.is_even)

    Eq << Eq[-1].this.rhs.apply(algebra.ne.given.is_zero)




if __name__ == '__main__':
    run()
# created on 2023-05-22
