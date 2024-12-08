from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    start, stop = S.of(Range)

    lower_bound = e < start
    upper_bound = e >= stop
    return Or(lower_bound, upper_bound)


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    e, a, b = Symbol(integer=True, given=True)
    Eq << apply(NotElement(e, Range(a, b)))

    Eq <<= ~Eq[0] & Eq[1]

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.to.And)

    Eq << Algebra.And.to.Or.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-06-06
# updated on 2023-05-14
