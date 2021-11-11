from util import *


@apply
def apply(imply):
    e, S = imply.of(NotElement)
    A, B = S.of(Union)
    return NotElement(e, A), NotElement(e, B)


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol(integer=True, given=True)
    B, A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(NotElement(e, B | A))

    Eq << sets.notin.notin.imply.notin.union.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2021-06-05
# updated on 2021-06-05
