from util import *


def merge(given):
    function, *limits = given.of(All)

    limit_slice, limit_index = limits

    if not limit_slice[0].is_Sliced:
        limit_index, limit_slice = limits

    x_slice, space = limit_slice
    _domain, n = space.of(CartesianSpace)

    x, slices = x_slice.of(Sliced)

    if len(limit_index) == 3:
        x_index, a, b = limit_index
        domain = x_index.range(a, b)
        S[x], index = x_index.args
    else:
        x_index, domain = limit_index
        if x_index.is_Sliced:
            domain, size = domain.of(CartesianSpace)
            assert size == x_index.shape[0]
            S[x], index = x_index.args
        else:
            S[x], index = x_index.of(Indexed)

    assert _domain == domain

    start, stop = slices
    if index == stop:
        stop += 1
    elif index == start - 1:
        start = index
    else:
        _start, S[start] = index
        start = _start

    return All[x[start:stop]:CartesianSpace(domain, stop - start)](function)


@apply
def apply(given):
    return merge(given)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True)
    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    Eq << apply(All[x[:n]:CartesianSpace(Interval(a, b), n), x[n]:Interval(a, b)](f(x[:n + 1]) > 0))

    Eq << Algebra.All.of.Imply.apply(Eq[1])

    Eq << Eq[-1].this.lhs.apply(Sets.In_CartesianSpace.to.All.In)

    Eq << Eq[-1].this.lhs.apply(Algebra.All.to.And.All.split, cond={n})

    Eq << Algebra.All.to.Imply.apply(Eq[0])

    Eq << Eq[-1].this.find(Element[CartesianSpace]).apply(Sets.In_CartesianSpace.of.All.In)





if __name__ == '__main__':
    run()

# created on 2018-12-09
# updated on 2023-08-20
