from util import *



@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])
    return Equal(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), complex=True)

    Eq << apply(All[i:n](Equal(f(i), g(i))))

    i_ = Symbol.i(domain=Range(n))

    Eq << Eq[0].limits_subs(i, i_)

    Eq << Eq[1].this.lhs.limits_subs(i, i_)

    Eq << Eq[-1].this.rhs.limits_subs(i, i_)

    Eq << Eq[-1].this.lhs.subs(Eq[2])


if __name__ == '__main__':
    run()

# created on 2018-02-18
# updated on 2018-02-18
