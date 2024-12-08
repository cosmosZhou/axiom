from util import *


@apply
def apply(eq_R):
    from Axiom.Keras.Eq_Lamda.to.Dot.eq.Lamda.position_representation.rotary import extract
    (Ri, d), b, (i, j, k) = extract(eq_R)
    return Equal(Ri.T @ Ri.subs(i, j), Ri.subs(i, j - i))

@prove(slow=True)
def prove(Eq):
    from Axiom import Discrete, Algebra, Sets, Geometry
    from Axiom.Keras.Eq_Lamda.to.Dot.eq.Lamda.position_representation.rotary import rotary_matrix
    # b denotes 10000
    b = Symbol(integer=True, positive=True)
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

    Eq.lhs = Eq[-1].this.rhs.apply(Discrete.Dot.eq.Lamda)

    A = Symbol(Eq.lhs.find(Sum))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def.this.find(Piecewise).apply(Algebra.Piece.subs, [0, 1])

    Eq << Eq[-1].this.find(Piecewise[2]).apply(Algebra.Piece.subs, [0, 1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.halve)

    Eq.el_to_et = Eq[-1].find(Element).this.apply(Sets.In_Intersect.equ.And)

    Eq.el_to_et_1 = Eq[-1].rhs.args[1].find(Element).this.apply(Sets.In_Intersect.equ.And)

    Eq.el_finite_mul = Eq.el_to_et.find(Element[FiniteSet]).this.apply(Sets.In.FiniteSet.Mul, 2)

    Eq.el_finite_mul_1 = Eq.el_to_et_1.find(Element[FiniteSet]).this.apply(Sets.In.FiniteSet.Mul, 2)

    Eq <<= Eq.el_to_et.find(Element[Range]).this.apply(Sets.In.Range.Mul.dilated, 2), \
        Eq.el_to_et_1.find(Element[Range]).this.apply(Sets.In.Range.Mul.dilated, 2).this.rhs.apply(Sets.In.Add, 1)

    Eq.el_Range_mul = Eq[-2].this.rhs.apply(Sets.In_Range.equ.And.split.Range)

    Eq.el_Range_mul_1 = Eq[-1].this.rhs.apply(Sets.In_Range.equ.And.split.Range)

    Eq << Eq[-3].subs(Eq.el_to_et, Eq.el_to_et_1, Eq.el_finite_mul, Eq.el_Range_mul, Eq.el_finite_mul_1, Eq.el_Range_mul_1)

    Eq << Eq[-1].this.find(Equal[Symbol - 1, Symbol]) + 1

    Eq << Eq[-1].this.find(Equal[Symbol - 1, Symbol - 1]) + 1

    Eq << Eq[-1].this.find(Element[Symbol - 1, FiniteSet]).apply(Sets.In.Add, 1, simplify=None)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.nest, pivot=slice(1, None))

    Eq << Eq[-1].this.find(Equal[1]).apply(Algebra.Eq_odd.equ.Ne.Zero)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(Algebra.Piece.nest)

    Eq << Eq[-1].this.rhs.find(Piecewise).find(Piecewise).apply(Algebra.Piece.unnest)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.nest, 1)

    Eq << Eq[-1].this.rhs.args[1].find(Piecewise).apply(Algebra.Piece.unnest)

    Eq.A_def_simplified = Eq[-1].this.rhs.args[1].find(Piecewise).apply(Algebra.Piece.swap)

    B = Symbol(Eq.lhs.find(Sum[2]))
    Eq.B_def = B.this.definition

    Eq << Eq.B_def.this.find(Piecewise).apply(Algebra.Piece.subs, [0, 1])

    Eq << Eq[-1].this.find(Piecewise[2]).apply(Algebra.Piece.subs, [0, 1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.halve)

    Eq << Eq[-1].this.find(Equal[Symbol + 1, Symbol]) - 1

    Eq << Eq[-1].this.find(Equal[Symbol + 1, Symbol + 1]) - 1

    Eq << Eq[-1].subs(Eq.el_to_et, Eq.el_to_et_1, Eq.el_finite_mul, Eq.el_Range_mul, Eq.el_finite_mul_1, Eq.el_Range_mul_1)

    Eq << Eq[-1].this.find(Element[Symbol - 1, FiniteSet]).apply(Sets.In.Add, 1)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.nest, pivot=slice(1, None))

    Eq << Eq[-1].this.find(Equal[1]).apply(Algebra.Eq_odd.equ.Ne.Zero)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(Algebra.Piece.nest)

    Eq << Eq[-1].this.rhs.find(Piecewise).find(Piecewise).apply(Algebra.Piece.unnest)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.nest, 1)

    Eq << Eq[-1].this.rhs.args[1].find(Piecewise).apply(Algebra.Piece.unnest)

    Eq << Eq[-1].this.rhs.find(Piecewise).find(Piecewise).apply(Algebra.Piece.swap)

    Eq << Eq[-1] + Eq.A_def_simplified

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.Piece.eq.Piece, deep=True, simplify=None)

    Eq <<= Eq[-1].rhs.find(Sin * Sin + Cos * Cos).this.apply(Geometry.Add.eq.Cos), \
        Eq[-1].rhs.find(Sin * Cos - Sin * Cos).this.apply(Geometry.Sub.eq.Sin), \
        Eq[-1].rhs.args[1].find(Sin * Sin + Cos * Cos).this.apply(Geometry.Add.eq.Cos), \
        Eq[-1].rhs.args[1].find(Sin * Cos - Sin * Cos).this.apply(Geometry.Sub.eq.Sin)

    Eq << Eq[-5].subs(*Eq[-4:])

    Eq << Eq[-1].this.find(Equal[Symbol, Symbol + 1]) - 1

    Eq << Eq[-1].this.rhs.find(Piecewise, Piecewise).apply(Algebra.Piece.subs, [0, 1], reverse=True)

    Eq << Eq[-1].this.rhs.args[1].find(Piecewise).apply(Algebra.Piece.subs, [0, 1], reverse=True)

    Eq <<= Eq[-1].find(Cos[~Add]).this.apply(Algebra.Add.eq.Mul), \
        Eq[-1].rhs.args[1].find(Cos[~Add]).this.apply(Algebra.Add.eq.Mul), \
        Eq[-1].rhs.args[1].find(Sin[~Add]).this.apply(Algebra.Add.eq.Mul)

    Eq << Eq[-4].this.rhs.subs(*Eq[-3:])

    Eq << Eq[-1].this.find(Equal[Symbol - 1, Symbol]) + 1

    Eq <<= Eq[-1].find(Cos).this.apply(Geometry.Cos.Neg), \
        Eq[-1].find(Sin).this.apply(Geometry.Sin.eq.Neg.Sin), \
        Eq[-1].rhs.args[1].find(Cos).this.apply(Geometry.Cos.Neg), \
        Eq[-1].rhs.args[1].find(Sin).this.apply(Geometry.Sin.eq.Neg.Sin)

    Eq << Eq[-5].this.rhs.subs(*Eq[-4:])

    Eq << Eq.lhs.subs(Eq[-1].subs(Eq.A_def, Eq.B_def))

    Eq << Eq[-1].this.rhs().expr.args[0]().find(Element).simplify()

    Eq << Eq[-1].this.rhs().expr.args[1]().find(Element).simplify()

    Eq << Eq[0].subs(i, j - i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Lamda.limits.swap.subs).this.rhs.expr.simplify()

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-3], Eq[-1])







if __name__ == '__main__':
    run()
# created on 2023-05-30
# updated on 2023-09-16
