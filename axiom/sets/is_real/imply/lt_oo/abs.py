from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    S[-oo], S[oo] = R.of(Interval)
    assert x.is_extended_real
    return Abs(x) < oo


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(extended_real=True)
    Eq << apply(Element(x, Interval(-oo, oo)))

    Eq << Eq[1].this.apply(sets.abs_lt_oo.to.is_real)

    


if __name__ == '__main__':
    run()
# created on 2023-04-16
