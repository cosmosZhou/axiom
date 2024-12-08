from util import *


@apply
def apply(cond0, cond1):
    x, y = cond0.args
    a, b = cond1.args

    assert x.is_integer
    assert y.is_integer
    assert a.is_integer
    assert b.is_integer

    if cond0.is_Less:
        # x < y
        if cond1.is_Greater:
            # a > b
            if x == a:
                e = x
                s = Range(b + 1, y)
            else:
                ...
        elif cond1.is_Less:
            # a < b
            if y == a:
                e = a
                s = Range(x + 1, b)
        # x < y
        if cond1.is_GreaterEqual:
            # a >= b
            if x == a:
                e = x
                s = Range(b, y)
            else:
                ...
    elif cond0.is_LessEqual:
        # x < y
        if cond1.is_GreaterEqual:
            # a >= b
            if x == a:
                e = x
                s = Range(b, y + 1)
            else:
                ...


    return Element(e, s)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b = Symbol(integer=True)
    Eq << apply(a < x, x < b)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.Lt.Lt.to.In.Range)

    Eq << Eq[-1].this.rhs.apply(Sets.In_Range.to.And)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.to.Gt.relax)

    Eq << Eq[-1].this.find(Greater).reversed




if __name__ == '__main__':
    run()
# created on 2021-12-17
# updated on 2023-05-21
