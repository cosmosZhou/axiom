from util import *


@apply
def apply(given):
    n, (__n, (_n, a, b)) = given.of(Element[Cup[FiniteSet[2 * Expr], Tuple[Floor, Floor + 1]]])

    assert n == _n == __n
    a = 2 * a - 1
    b = 2 * b
# i ∈ [d + j; n) & j ∈ [a; -d + n)
    return Equal(n % 2, 0), Element(n, Range(a, b + 1))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    a, b, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(n, imageset(n, 2 * n, Range((a + 1) // 2, b // 2 + 1))))

    S = Symbol(Eq[0].rhs)
    Eq << S.this.definition

    Eq << Eq[-1].this.rhs.limits_subs(n, n / 2)

    Eq << Element(n, S, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq.contains = Eq[-1].subs(Eq[-2]).simplify()

    Eq << Sets.In.to.In.Mul.Range.apply(Eq.contains, 2)

    Eq << Sets.In_Range.to.And.apply(Eq[-1], right_open=False)

    Eq << Algebra.Ge.Ge.to.Ge.trans.apply(Eq[-2], Algebra.Mul_FloorDiv.ge.SubAdd_1.apply(a + 1, 2))

    Eq << Algebra.Le.Le.to.Le.trans.apply(Eq[-2], Algebra.LeFloor.apply(b / 2) * 2)

    Eq << Sets.Ge.Le.to.In.Range.apply(Eq[-2], Eq[-1])

    Eq << Subset(Eq.contains.rhs, Integers, plausible=True)

    Eq << Sets.In.Subset.to.In.apply(Eq.contains, Eq[-1])

    Eq << Sets.In.to.Any.Eq.apply(Eq[-1])

    Eq << Eq[-1] * 2

    Eq << Eq[-1] % 2


if __name__ == '__main__':
    run()

# created on 2018-05-27
