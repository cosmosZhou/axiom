from util import *



@apply
def apply(given):
    return Equal(Bool(given), 1)


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()

# created on 2020-11-03
