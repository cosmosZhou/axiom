from util import *


@apply
def apply(is_extended_real):
    x, R = is_extended_real.of(Element)
    a, b = R.of(Interval)
    right = b == oo and not R.right_open
    left = a == -oo and not R.left_open
    if right and left:
        return Element(x, Reals) | Equal(x, oo) | Equal(x, -oo)
    if right:
        return Element(x, R.copy(right_open=True)) | Equal(x, oo)
    if left:
        return Element(x, R.copy(left_open=True)) | Equal(x, -oo)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, ExtendedReals))

    Eq << sets.el_interval.imply.ou.apply(Eq[0], oo)

    Eq << Eq[-1].this.args[1].simplify()

    Eq << Eq[-1].this.args[1].apply(sets.el_interval.imply.ou, -oo, simplify=None, left_open=True)
    Eq << Eq[-1].this.args[-1].simplify()


if __name__ == '__main__':
    run()
# created on 2021-05-15
