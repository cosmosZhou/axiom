from util import *



@apply
def apply(given, *, cond=None):
    lhs, rhs = given.of(Infer)
    return Infer(cond | lhs, cond | rhs)


@prove
def prove(Eq):
    from axiom import algebra

    p, q, r = Symbol(bool=True)
    Eq << apply(Infer(p, q), cond=r)

    Eq << algebra.infer.then.ou.apply(Eq[0])

    Eq << algebra.infer.of.ou.apply(Eq[1])

    Eq << algebra.ou.of.et.apply(Eq[-1])

    Eq << algebra.ou.of.ou.apply(Eq[-1], slice(0, 3, 2))





if __name__ == '__main__':
    run()
# created on 2019-10-05
# updated on 2022-01-27
