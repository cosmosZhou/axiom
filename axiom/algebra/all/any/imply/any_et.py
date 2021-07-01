from util import *


@apply
def apply(forall, exists):
    if forall.is_Any:
        forall, exists = exists, forall

    fx, *limits_f = forall.of(All)
    fy, *limits_e = exists.of(Any)

    dict_f = forall.limits_dict
    dict_e = exists.limits_dict
    for key, domain_f in dict_f.items():
        assert key in dict_e

        domain_e = dict_e[key]

        if domain_f == []:
            domain_f = key.universalSet
        elif domain_f.is_boolean:
            domain_f = conditionset(key, domain_f)

        if domain_e == []:
            domain_e = key.universalSet
        elif domain_e.is_boolean:
            domain_e = conditionset(key, domain_e)

        assert domain_f.is_set
        assert domain_e.is_set

        assert domain_e in domain_f

    return Any(fx & fy, *limits_e)


@prove
def prove(Eq):
    from axiom import algebra
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(All[y:g(y) > 0](f(y) > 0), Any[y:g(y) > 1, x:f(x) > 0](g(x) > 0))

    Eq << algebra.any.given.any_et.apply(Eq[-1])

    Eq.any = algebra.any.imply.any_et.apply(Eq[1], simplify=False)

    Eq << algebra.all.imply.suffice.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.gt.given.gt.astrict, 1)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq.any.this.function.args[2].apply(algebra.cond.suffice.imply.cond.transit, Eq[-1])


if __name__ == '__main__':
    run()
