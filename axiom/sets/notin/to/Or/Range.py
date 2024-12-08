from util import *


@apply
def apply(given):
    x, rgn = given.of(NotElement)

    a, b = rgn.of(Range)
    if rgn.left_open:
        if rgn.right_open:
            return (x <= a) | (x >= b)
        return (x <= a) | (x > b)
    else:
        if rgn.right_open:
            return (x < a) | (x >= b)
        return (x < a) | (x > b)


@prove
def prove(Eq):
    from Axiom import Sets

    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(NotElement(x, Range(a, b)))

    Eq << Sets.Or.of.NotIn.Range.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-06-05
