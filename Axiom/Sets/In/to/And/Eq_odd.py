from util import *


@apply
def apply(given):
    n, (__n, (_n, a, b)) = given.of(Element[Cup[FiniteSet[2 * Expr + 1], Tuple[Floor, Floor + 1]]])
    assert n == _n == __n

    a = 2 * a
    b = 2 * b + 1

    return Equal(n % 2, 1), Element(n, Range(a, b + 1))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(n, imageset(n, 2 * n + 1, Range(a // 2, (b - 1) // 2 + 1))))

    S = Symbol(Eq[0].rhs)
    Eq << S.this.definition

    Eq << Eq[-1].this.rhs.limits_subs(n, (n - 1) / 2)

    Eq << Element(n, S, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq.contains = Eq[-1].subs(Eq[-2]).simplify()

    Eq << Sets.In.to.In.Mul.Range.apply(Eq.contains, 2)

    Eq.greater_than, Eq.less_than = Sets.In_Range.to.And.apply(Eq[-1], right_open=False)

    Eq.strict_greater_than = Algebra.Ge.to.Gt.relax.apply(Eq.greater_than)

    Eq << Algebra.Gt.Ge.to.Gt.trans.apply(Eq.strict_greater_than, Algebra.Mul_FloorDiv.ge.SubAdd_1.apply(a, 2))

    Eq << Algebra.Gt.to.Ge.strengthen.apply(Eq[-1])

    Eq << Algebra.LeFloor.apply((b - 1) / 2) * 2 + 1

    Eq << Algebra.Le.Le.to.Le.trans.apply(Eq.less_than, Eq[-1])

    Eq << Sets.Ge.Le.to.In.Range.apply(Eq[-3], Eq[-1])

    Eq << Subset(Eq.contains.rhs, Integers, plausible=True)

    Eq << Sets.In.Subset.to.In.apply(Eq.contains, Eq[-1])

    Eq << Sets.In.to.Any.Eq.apply(Eq[-1])

    Eq << Eq[-1] * 2 + 1

    Eq << Eq[-1] % 2


if __name__ == '__main__':
    run()

# created on 2018-05-30