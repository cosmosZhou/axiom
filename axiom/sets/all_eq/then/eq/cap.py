from util import *



@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])

    return Equal(Cap(lhs, *limits).simplify(), Cap(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Function(shape=(), etype=dtype.integer)
    Eq << apply(All[i:n](Equal(f(i), g(i))))

    Eq.hypothesis = Infer(Eq[0], Eq[1], plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << algebra.infer.then.infer.et.both_sided.apply(Eq.hypothesis, cond=Equal(f(n), g(n)))

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.of.all.push)

    Eq << Eq[-1].this.rhs.apply(sets.eq.eq.then.eq.cap.push)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.infer.then.cond.induct.apply(Eq[-1], n=n, start=1)


    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[0], Eq.hypothesis)




if __name__ == '__main__':
    run()

# created on 2021-01-11
# updated on 2023-05-21
