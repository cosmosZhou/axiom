from util import *


@apply
def apply(eq, all):
    (w, i, j), (S[i], S[j]) = eq.of(Equal[Indexed, SwapMatrix])
    ((S[w[0, j]], x), s), (S[x], S[s]) = all.of(All[Element[MatMul]])

    return All[x:s](Element(w[i, j] @ x, s))


@prove
def prove(Eq):
    from axiom import algebra, discrete, sets

    n = Symbol(domain=Range(2, oo))
    S = Symbol(etype=dtype.integer[n])
    x = Symbol(**S.element_symbol().type.dict)
    w = Symbol(real=True, shape=(n, n, n, n))
    i, j = Symbol(integer=True)
    Eq << apply(Equal(w[i, j], SwapMatrix(n, i, j)), All[x:S](Element(w[0, j] @ x, S)))

    j_ = j.copy(domain=Range(n))
    Eq.given = Eq[1].subs(j, j_)

    i_ = i.copy(domain=Range(n))
    Eq.given_i = Eq.given.subs(j_, i_)

    Eq << algebra.all.imply.ou.subs.apply(Eq.given, x, Eq.given_i.expr.lhs)

    Eq << algebra.cond.all.imply.all.et.apply(Eq[-1], Eq.given_i)

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=-1)

    Eq << algebra.all.imply.ou.subs.apply(Eq.given_i, x, Eq[-1].expr.lhs)

    Eq << algebra.cond.all.imply.all.et.apply(Eq[-2], Eq[-1])

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=1)

    Eq.final_statement = algebra.cond.imply.all.restrict.apply(Eq[-1], (i_,), (j_,))

    Eq << discrete.eq.lamda.swapMatrix.imply.all_eq.swap2.eq.apply(Eq[0])

    Eq << Eq[-1].this.expr @ x

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (Eq[-1].limits[0].args[1].args[1].arg,))

    Eq << algebra.all.all.imply.all.et.apply(Eq.final_statement, Eq[-1])

    Eq.i_complement = Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)

    Eq.plausible = All(Element(w[i, j] @ x, S), (x, S), (j, Range(1, n)), plausible=True)

    Eq << algebra.all.given.et.apply(Eq.plausible, cond=i.set, wrt=j)

    Eq << sets.imply.eq.intersect.apply(i, Range(1, n))

    Eq << Eq[-2].this.limits[1].subs(Eq[-1])



    Eq << Eq[-1].subs(Eq[0].subs(j, i)).simplify()

    Eq << discrete.eq.imply.eq.swapMatrix.swap.apply(Eq[0]).subs(j, 0)

    Eq.given_i = algebra.cond.imply.all.restrict.apply(Eq.given_i, (i_,))

    Eq << Eq.given_i.subs(Eq[-1].reversed)

    Eq << algebra.all.given.et.apply(Eq[2], cond=Equal(j, 0))





if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-25
# updated on 2023-08-26
