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
    from Axiom import Set, Algebra

    a, b, i, j, n, d = Symbol(integer=True)
    Eq << apply(Element(n, imageset(n, 2 * n, Range((a + 1) // 2, b // 2 + 1))))

    S = Symbol(Eq[0].rhs)
    Eq << S.this.definition

    Eq << Eq[-1].this.rhs.limits_subs(n, n / 2)

    Eq << Element(n, S, plausible=True)

    Eq << Eq[-1].this.rhs.definition

    Eq.contains = Eq[-1].subs(Eq[-2]).simplify()

    Eq << Set.Mem.Mul.Range.of.Mem.apply(Eq.contains, 2)

    Eq << Set.And.of.Mem_Range.apply(Eq[-1], right_open=False)

    Eq << Algebra.Ge.of.Ge.Ge.apply(Eq[-2], Algebra.Mul_FloorDiv.ge.SubAdd_1.apply(a + 1, 2))

    Eq << Algebra.Le.of.Le.Le.apply(Eq[-2], Algebra.LeFloor.apply(b / 2) * 2)

    Eq << Set.Mem.Range.of.Ge.Le.apply(Eq[-2], Eq[-1])

    Eq << Subset(Eq.contains.rhs, Integers, plausible=True)

    Eq << Set.Mem.of.Mem.Subset.apply(Eq.contains, Eq[-1])

    Eq << Set.Any.Eq.of.Mem.apply(Eq[-1])

    Eq << Eq[-1] * 2

    Eq << Eq[-1] % 2


if __name__ == '__main__':
    run()

# created on 2018-05-27
