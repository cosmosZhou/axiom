from util import *


@apply
def apply(is_negative, eq, *, simplify=True):
    x = is_negative.of(Expr < 0)
    lhs, rhs = eq.of(Equal)
    if simplify and lhs.is_Add:
        lhs = Add(*(arg / x for arg in lhs.args))
    else:
        lhs /= x
        
    if simplify and rhs.is_Add:
        rhs = Add(*(arg / x for arg in rhs.args))
    else:
        rhs /= x

    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    f, g, h = Function(real=True)
    Eq << apply(f(x) < 0, Equal(g(x) * f(x), h(x) * f(x) + x))

    Eq << algebra.lt_zero.imply.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.eq.imply.eq.div.apply(Eq[-1], Eq[1])

    
    


if __name__ == '__main__':
    run()
# created on 2020-01-16
# updated on 2023-05-02
