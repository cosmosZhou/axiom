from util import *


@apply(simplify=False)
def apply(given, t):
    lhs, rhs = given.of(Infer)
    domain = given.domain_defined(t)
    cond = Element(t, domain)
    return Infer(cond & lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f, g = Symbol(bool=True, shape=(n,))
    Eq << apply(Infer(f[k], g[k]), k)

    Eq << algebra.infer.then.infer.et.both_sided.apply(Eq[0], cond=Eq[1].find(Element))

    Eq << Eq[-1].this().rhs.find(Element).simplify()


if __name__ == '__main__':
    run()
# created on 2023-04-13
