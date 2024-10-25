from util import *


# given : A & B = A | B => A = B


@apply
def apply(given):
    (x, y), ((a, S[0]), (S[a], S[1])) = given.of(Equal[FiniteSet, FiniteSet[Indexed, Indexed]])
    return Equal(Matrix([x, y]), Matrix([a[1 - KroneckerDelta(a[0], x)], a[KroneckerDelta(a[0], x)]]))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(etype=dtype.complex, given=True)
    a = Symbol(etype=dtype.complex, shape=(oo,), given=True)
    Eq << apply(Equal({x, y}, {a[0], a[1]}))

    Eq << algebra.eq.of.et.split.matrix.apply(Eq[1])

    Eq << Element(x, {x, y}, plausible=True)

    Eq.x_contains = Eq[-1].subs(Eq[0])

    Eq << sets.el.then.ou.split.finiteset.two.apply(Eq.x_contains, simplify=False)

    Eq << Eq[2].apply(algebra.cond.of.et.ou, cond=Equal(x, a[0]))

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].this.apply(algebra.ne.cond.then.cond.subs, ret=0), Eq[-1].this.apply(algebra.eq.cond.then.cond.delta, ret=0)

    Eq << Eq[-1].apply(sets.ne.ne.then.notin, simplify=False)

    Eq <<= Eq.x_contains & Eq[-1]

    Eq << Eq[3].apply(algebra.cond.of.et.ou, cond=Equal(x, a[0]))

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq.a00, Eq.a01 = Eq[-2].this.apply(algebra.ne.cond.then.cond.subs, ret=0), Eq[-1].this.apply(algebra.eq.cond.then.cond.delta, ret=0)

    Eq << Eq.a00.apply(sets.ne.ne.then.notin, simplify=False)

    Eq << Element(a[0], {a[0], a[1]}, plausible=True)

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Element(y, {x, y}, plausible=True)

    Eq.y_contains = Eq[-1].subs(Eq[0])

    Eq << sets.el.then.ou.split.finiteset.two.apply(Eq.y_contains, simplify=False)

    Eq <<= Eq[-1] & Eq.a01

    Eq << Element(a[1], {a[0], a[1]}, plausible=True)

    Eq << Eq[-1].subs(Eq[0].reversed)

    Eq << sets.el.then.ou.split.finiteset.two.apply(Eq[-1], simplify=False)

    Eq <<= Eq[-1] & Eq[-4]

    Eq <<= Infer(And(*Eq[-1].args[::2]), And(*Eq[-1].args[::2]), plausible=True), Infer(And(*Eq[-1].args[1::2]), And(*Eq[-1].args[1::2]), plausible=True)

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.eq.then.eq.trans), Eq[-1].this.rhs.apply(algebra.eq.ne.then.ne.trans)

    Eq << algebra.infer.infer.then.infer.et.apply(Eq[-2], Eq[-1])

    Eq << ~Eq[-1]




if __name__ == '__main__':
    run()

# created on 2021-04-02
# updated on 2023-05-17
