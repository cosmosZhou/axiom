from util import *


@apply
def apply(cond0, cond1):
    x, y = cond0.args
    a, b = cond1.args

    if cond0.is_Less:
        # x < y
        if cond1.is_Greater:
            # a > b
            if x == a:
                e = x
                left_open = True
                right_open = True
                start = b
                stop = y
            else:
                ...
        elif cond1.is_Less:
            # a < b
            if y == a:
                e = a
                left_open = True
                right_open = True
                start = x
                stop = b
        # x < y
        if cond1.is_GreaterEqual:
            # a >= b
            if x == a:
                e = x
                left_open = False
                right_open = True
                start = b
                stop = y
            else:
                ...
    elif cond0.is_LessEqual:
        # x < y
        if cond1.is_GreaterEqual:
            # a >= b
            if x == a:
                e = x
                left_open = False
                right_open = False
                start = b
                stop = y
            else:
                ...


    return Element(e, Interval(start, stop, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b = Symbol(integer=True)
    Eq << apply(a < x, x < b)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.Lt.Lt.to.In.Interval)

    Eq << Eq[-1].this.rhs.apply(Sets.In_Interval.to.And)

    Eq << Eq[-1].this.find(Greater).reversed




if __name__ == '__main__':
    run()
# created on 2022-01-07
# updated on 2023-05-21
