from util import *


@apply
def apply(all_a, all_b):
    from sympy.concrete.limits import limits_intersect
    fn, *limits_a = all_a.of(All)
    _fn, *limits_b = all_b.of(All)

    limits = limits_intersect(limits_a, limits_b)
    return All(fn & _fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    e = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f, g = Function(integer=True)
    Eq << apply(All[e:A](f(e) > 0), All[e:B](g(e) > 0))

    Eq << algebra.all_et.of.et.all.apply(Eq[-1])

    Eq << algebra.all.of.all.limits.relax.apply(Eq[-2], A)

    Eq << algebra.all.of.all.limits.relax.apply(Eq[-1], B)




if __name__ == '__main__':
    run()


# created on 2018-09-30
# updated on 2023-11-12
