from util import *

from axiom.keras.eq_lamda.then.eq.matmul.to.lamda.position_representation.rotary import rotary_matrix, extract

@apply
def apply(eq_R):
    (Ri, d), b, (i, j, k) = extract(eq_R)
    return Equal(Ri.T @ Ri.subs(i, j), Ri.subs(i, j - i))

@prove(slow=True)
def prove(Eq):
    from axiom import discrete, algebra, sets, geometry

    # n denotes sequence length (seq_length)
    # b denotes 10000
    n, b = Symbol(integer=True, positive=True)
    # d denotes embedding size which must be even
    d = Symbol(integer=True, positive=True, even=True)
    # i denotes token index
    # j denotes row index
    # k denotes column index
    i, j, k = Symbol(integer=True)
    # R denotes rotary matrix
    R = Function(shape=(d, d), real=True)
    Eq << apply(Equal(R(i), rotary_matrix(d, b, i, j, k)))

    Eq << Eq[0].T @ Eq[0].subs(i, j)

    Eq.lhs = Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    A = Symbol(Eq.lhs.find(Sum))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def.this.find(Piecewise).apply(algebra.piece.subs, [0, 1])

    Eq << Eq[-1].this.find(Piecewise[2]).apply(algebra.piece.subs, [0, 1])

    Eq << Eq[-1].this.rhs.apply(algebra.sum.halve)

    Eq.el_to_et = Eq[-1].find(Element).this.apply(sets.el_intersect.to.et)

    Eq.el_to_et_1 = Eq[-1].rhs.args[1].find(Element).this.apply(sets.el_intersect.to.et)

    Eq.el_finite_mul = Eq.el_to_et.find(Element[FiniteSet]).this.apply(sets.el.finiteset.mul, 2)

    Eq.el_finite_mul_1 = Eq.el_to_et_1.find(Element[FiniteSet]).this.apply(sets.el.finiteset.mul, 2)

    Eq <<= Eq.el_to_et.find(Element[Range]).this.apply(sets.el.range.mul.dilated, 2), \
        Eq.el_to_et_1.find(Element[Range]).this.apply(sets.el.range.mul.dilated, 2).this.rhs.apply(sets.el.add, 1)

    Eq.el_range_mul = Eq[-2].this.rhs.apply(sets.el_range.to.et.split.range)

    Eq.el_range_mul_1 = Eq[-1].this.rhs.apply(sets.el_range.to.et.split.range)

    Eq << Eq[-3].subs(Eq.el_to_et, Eq.el_to_et_1, Eq.el_finite_mul, Eq.el_range_mul, Eq.el_finite_mul_1, Eq.el_range_mul_1)

    Eq << Eq[-1].this.find(Equal[Symbol - 1, Symbol]) + 1

    Eq << Eq[-1].this.find(Equal[Symbol - 1, Symbol - 1]) + 1

    Eq << Eq[-1].this.find(Element[Symbol - 1, FiniteSet]).apply(sets.el.add, 1, simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.nest, pivot=slice(1, None))

    Eq << Eq[-1].this.find(Equal[1]).apply(algebra.is_odd.to.ne.zero)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(algebra.piece.nest)

    Eq << Eq[-1].this.rhs.find(Piecewise).find(Piecewise).apply(algebra.piece.unnest)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.nest, 1)

    Eq << Eq[-1].this.rhs.args[1].find(Piecewise).apply(algebra.piece.unnest)

    Eq.A_def_simplified = Eq[-1].this.rhs.args[1].find(Piecewise).apply(algebra.piece.swap)

    B = Symbol(Eq.lhs.find(Sum[2]))
    Eq.B_def = B.this.definition

    Eq << Eq.B_def.this.find(Piecewise).apply(algebra.piece.subs, [0, 1])

    Eq << Eq[-1].this.find(Piecewise[2]).apply(algebra.piece.subs, [0, 1])

    Eq << Eq[-1].this.rhs.apply(algebra.sum.halve)

    Eq << Eq[-1].this.find(Equal[Symbol + 1, Symbol]) - 1

    Eq << Eq[-1].this.find(Equal[Symbol + 1, Symbol + 1]) - 1

    Eq << Eq[-1].subs(Eq.el_to_et, Eq.el_to_et_1, Eq.el_finite_mul, Eq.el_range_mul, Eq.el_finite_mul_1, Eq.el_range_mul_1)

    Eq << Eq[-1].this.find(Element[Symbol - 1, FiniteSet]).apply(sets.el.add, 1)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.nest, pivot=slice(1, None))

    Eq << Eq[-1].this.find(Equal[1]).apply(algebra.is_odd.to.ne.zero)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(algebra.piece.nest)

    Eq << Eq[-1].this.rhs.find(Piecewise).find(Piecewise).apply(algebra.piece.unnest)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.nest, 1)

    Eq << Eq[-1].this.rhs.args[1].find(Piecewise).apply(algebra.piece.unnest)

    Eq << Eq[-1].this.rhs.find(Piecewise).find(Piecewise).apply(algebra.piece.swap)

    Eq << Eq[-1] + Eq.A_def_simplified

    Eq << Eq[-1].this.rhs.apply(algebra.add.piece.to.piece, deep=True, simplify=None)

    Eq <<= Eq[-1].rhs.find(Sin * Sin + Cos * Cos).this.apply(geometry.add.to.cos), \
        Eq[-1].rhs.find(Sin * Cos - Sin * Cos).this.apply(geometry.sub.to.sin), \
        Eq[-1].rhs.args[1].find(Sin * Sin + Cos * Cos).this.apply(geometry.add.to.cos), \
        Eq[-1].rhs.args[1].find(Sin * Cos - Sin * Cos).this.apply(geometry.sub.to.sin)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[-1].this.find(Equal[Symbol, Symbol + 1]) - 1

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(algebra.piece.subs, [0, 1], reverse=True)

    Eq << Eq[-1].this.rhs.args[1].find(Piecewise).apply(algebra.piece.subs, [0, 1], reverse=True)

    Eq <<= Eq[-1].find(Cos[~Add]).this.apply(algebra.add.to.mul), \
        Eq[-1].rhs.args[1].find(Cos[~Add]).this.apply(algebra.add.to.mul), \
        Eq[-1].rhs.args[1].find(Sin[~Add]).this.apply(algebra.add.to.mul)

    Eq << Eq[-4].this.rhs.subs(*Eq[-3:])

    Eq << Eq[-1].this.find(Equal[Symbol - 1, Symbol]) + 1

    Eq <<= Eq[-1].find(Cos).this.apply(geometry.cos.neg), \
        Eq[-1].find(Sin).this.apply(geometry.sin.to.neg.sin), \
        Eq[-1].rhs.args[1].find(Cos).this.apply(geometry.cos.neg), \
        Eq[-1].rhs.args[1].find(Sin).this.apply(geometry.sin.to.neg.sin)

    Eq << Eq[-5].this.rhs.subs(*Eq[-4:])

    Eq << Eq.lhs.subs(Eq[-1].subs(Eq.A_def, Eq.B_def))

    Eq << Eq[-1].this.rhs().expr.args[0]().find(Element).simplify()

    Eq << Eq[-1].this.rhs().expr.args[1]().find(Element).simplify()

    Eq << Eq[0].subs(i, j - i)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.limits.swap.subs).this.rhs.expr.simplify()

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-3], Eq[-1])







if __name__ == '__main__':
    run()
# created on 2023-05-30
# updated on 2023-09-16
