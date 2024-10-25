from util import *


@apply
def apply(given):
    e, s = given.of(NotElement)
    space, *shape = s.of(CartesianSpace)
    k = given.generate_var(integer=True)
    n = e.shape[0]
    return Exists[k:n](NotElement(e[k], CartesianSpace(space, *shape[1:])).simplify())


@prove
def prove(Eq):
    from axiom import sets

    n, m = Symbol(positive=True, integer=True, given=True)
    x = Symbol(integer=True, shape=(n,), given=True)
    i = Symbol(integer=True)
    Eq << apply(NotElement(Lamda[i:n](x[i]), CartesianSpace(Range(0, m), n)))

    Eq << ~Eq[0]

    Eq << sets.el_cartesianSpace.then.all.el.apply(Eq[-1], simplify=None)

    Eq << ~Eq[-1]




if __name__ == '__main__':
    run()
# created on 2023-07-02
# updated on 2023-08-20
