from util import *



def transit(b_eq_x, x_eq_a, reverse=False):
    b, x = b_eq_x.of(Iff)
    _x, a = x_eq_a.of(Iff)
    if x != _x:
        if _x == b:
            b, x = x, b
        elif a == b:
            b, x, _x, a = x, b, a, _x
        elif x == a:
            _x, a = a, _x

        assert x == _x

    if reverse:
        b, a = a, b
    return Iff(b, a)


@apply
def apply(equivalent_0, equivalent_1, reverse=False):
    return transit(equivalent_0, equivalent_1, reverse=reverse)


@prove
def prove(Eq):
    from Axiom import Algebra
    a, x, b = Symbol(etype=dtype.real)
    f = Function(real=True)

    Eq << apply(Iff(f(b) > 0, f(x) > 0), Iff(f(x) > 0, f(a) > 0))

    Eq << Algebra.Iff.of.And.apply(Eq[-1])

    Eq << Algebra.Iff.to.Imply.apply(Eq[0])

    Eq << Algebra.Iff.to.Imply.apply(Eq[1])

    Eq << Algebra.Imply.Imply.to.Imply.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Iff.to.Given.apply(Eq[0])

    Eq << Algebra.Iff.to.Given.apply(Eq[1])

    Eq << Algebra.Given.Given.to.Given.trans.apply(Eq[-2], Eq[-1])

if __name__ == '__main__':
    run()
# created on 2019-09-12
