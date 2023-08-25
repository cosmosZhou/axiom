from util import *


def rewrite(self):
    e, (space, *shape) = self.of(Element[CartesianSpace])
    indices, limits = ZeroMatrix(*shape).variables_with_limits()
    return ForAll(Element(e[indices], space), *limits)

@apply
def apply(given):
    return rewrite(given)


@prove
def prove(Eq):
    from axiom import sets

    n, m = Symbol(positive=True, integer=True)
    x = Symbol(integer=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(Element(Lamda[i:n](x[i]), CartesianSpace(Range(0, m), n)))

    Eq << Eq[0].this.apply(sets.el_cartesianSpace.to.all.el)


if __name__ == '__main__':
    run()
# created on 2023-08-20
