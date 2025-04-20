from util import *


@apply
def apply(given, right_open=True):
    x, (a, b) = given.of(Element[Range])
    if right_open:
        return x >= a, x < b
    else:
        return x >= a, x <= b - 1


@prove
def prove(Eq):
    from Axiom import Set

    x = Symbol(real=True, given=True)
    a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)), False)

    Eq << Set.Le.of.Mem_Range.stop.apply(Eq[0])

    Eq << Set.Ge.of.Mem_Range.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-05-05


from . import split
