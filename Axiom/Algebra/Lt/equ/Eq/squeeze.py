from util import *



@apply
def apply(given):
    x, a = given.of(Less)
    assert x.is_integer and a.is_integer
    a -= 1

    assert x >= a
    return Equal(x, a)


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(domain=Range(1, oo))

    Eq << apply(Less(x, 2))

    Eq << Algebra.Iff.of.And.apply(Eq[-1])

    Eq << Eq[-2].this.apply(Algebra.Imply.equ.Or)

    Eq << Eq[-1].this.apply(Algebra.Given.equ.Or)



if __name__ == '__main__':
    run()

# created on 2020-01-10