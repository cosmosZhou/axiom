from util import *


@apply
def apply(imply):
    limits = None
    eqs = []
    for exist in imply.of(Or):
        fn, *_limits = exist.of(Any)
        if limits is None:
            limits = _limits
        else:
            assert limits == _limits
        eqs.append(fn)

    return Any(Or(*eqs), *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)

    f, g = Function(integer=True)

    Eq << apply(Or(Any[x:A]((g(x) > 0)), Any[x:A](f(x) > 0)))

    Eq << algebra.iff.of.et.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(algebra.any_ou.of.ou.any)

    Eq << Eq[-1].this.rhs.apply(algebra.any_ou.then.ou.any)


if __name__ == '__main__':
    run()

# created on 2020-02-20
