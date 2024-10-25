from util import *



@apply
def apply(given):
    expr = given.of(Unequal[One])
    n, S[2] = expr.of(Mod)
    return Equal(expr, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(integer=True)

    Eq << apply(Unequal(n % 2, 1))

    Eq << sets.then.el.mod.apply(n % 2)

    Eq << sets.el_range.then.ou.apply(Eq[-1])

    Eq << algebra.cond.ou.then.cond.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-10-11
