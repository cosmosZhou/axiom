from util import *


@apply
def apply(ge_ij, ge_i):
    j, i = ge_ij.of(GreaterEqual)
    S[i], (n, (S[n], u)) = ge_i.of(Expr >= Expr - Min)

    assert i in Range(n)
    assert j in Range(n)
    return Element(j - i, Range(0, u))


@prove
def prove(Eq):
    from Axiom import Set

    n, u = Symbol(domain=Range(2, oo), given=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(j >= i, i >= n - Min(n, u))

    Eq << Set.Mem_Range.given.And.apply(Eq[-1])

    Eq << Eq[0] - i

    Eq << -Eq[-1] + j

    Eq << ~Eq[-1]

    Eq << Set.Mem.Range.of.Le.Ge.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2022-01-02
