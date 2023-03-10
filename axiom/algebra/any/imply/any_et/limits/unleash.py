from util import *


def limits_cond(limits, index):
    x, *ab = limits[index]
    assert ab
    if len(ab) == 1:
        [cond] = ab
        if cond.is_set:
            cond = Element(x, domain)
    else:
        a, b = ab
        if b.is_set:
            cond = Element(x, b) & a
        else:
            cond = Element(x, Range(a, b) if x.is_integer else Interval(a, b))
    return x, cond

@apply
def apply(given, index=None):
    function, *limits = given.of(Any)
    if index is None:
        cond = given.limits_cond
        limits = given.variables
    else:
        x, cond = limits_cond(limits, index)
        limits[index] = (x,)

    return Any((function & cond).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(real=True)
    f, g, h = Function(shape=(), integer=True)
    Eq << apply(Any[x:f(x) > 0, y:g(y) > 0](h(x, y) > 0))

    A = Symbol(conditionset(x, f(x) > 0))
    B = Symbol(conditionset(y, g(y) > 0))
    Eq << Any[x:A, y:B](h(x, y) > 0, plausible=True)

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << Eq[-1].this.limits[1][1].definition

    Eq << sets.any.imply.any_et.apply(Eq[-2], simplify=False)

    Eq << Bool(Eq[-1].expr).this.arg.args[1].rhs.definition

    Eq << Eq[-1].this.rhs.arg.args[2].rhs.definition

    Eq << algebra.eq_bool.imply.iff.apply(Eq[-1])

    Eq << algebra.iff.cond.imply.cond.subs.apply(Eq[-1], Eq[-4])


if __name__ == '__main__':
    run()

# created on 2018-03-23
