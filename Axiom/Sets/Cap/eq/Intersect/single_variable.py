from util import *


@apply
def apply(self):
    fx, (x, s) = self.of(Cap)
    return Equal(self, fx.as_multiple_terms(x, s, cls=Cap))


@prove
def prove(Eq):
    from Axiom import Sets, Algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f, g = Function(etype=dtype.real)
    Eq << apply(Cap[x:B](Piecewise((f(x, y), Element(x, A)), (g(x, y), True))))

    Eq << Sets.Eq.of.And.Imply.apply(Eq[0], wrt='y')

    Eq <<= Eq[-2].this.lhs.apply(Sets.In_Cap.to.All_In), \
    Eq[-1].this.rhs.apply(Sets.In_Cap.of.All_In)

    Eq <<= Eq[-2].this.lhs.expr.apply(Algebra.Cond_Piece.to.Or), \
    Eq[-1].this.rhs.expr.apply(Algebra.Cond_Piece.of.Or)

    Eq <<= Eq[-2].this.rhs.apply(Sets.In_Intersect.of.And.In, simplify=None), \
    Eq[-1].this.lhs.apply(Sets.In_Intersect.to.And.In, simplify=None)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Sets.In_Cap.of.All_In), \
    Eq[-1].this.lhs.find(Element).apply(Sets.In_Cap.to.All_In)

    Eq <<= Eq[-2].this.rhs.find(Element).apply(Sets.In_Cap.of.All_In), \
    Eq[-1].this.lhs.find(Element).apply(Sets.In_Cap.to.All_In)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.All.to.And.All.split, cond=A), Eq[-1].this.rhs.apply(Algebra.All.of.And.All.split, cond=A)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.All.equ.Imply), Eq[-1].this.rhs.args[0].apply(Algebra.All.equ.Imply)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(Sets.In.equ.And.st.Intersect, index=0, simplify=False), \
    Eq[-1].this.rhs.args[0].lhs.apply(Sets.In.equ.And.st.Intersect, index=0, simplify=False)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Imply.subs.Bool, index=0, invert=True), \
    Eq[-1].this.rhs.args[0].apply(Algebra.Imply.subs.Bool, index=0, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.args[1].apply(Sets.In.equ.And.st.Intersect), \
    Eq[-1].this.rhs.args[0].lhs.args[1].apply(Sets.In.equ.And.st.Intersect)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Imply.equ.All, wrt=x), \
    Eq[-1].this.rhs.args[0].apply(Algebra.Imply.equ.All, wrt=x)

    Eq <<= Eq[-2].this.lhs.args[1].apply(Algebra.All.equ.Imply), Eq[-1].this.rhs.apply(Algebra.All.equ.Imply)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.apply(Sets.In.equ.And.st.Complement), \
    Eq[-1].this.rhs.lhs.apply(Sets.In.equ.And.st.Complement)

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Imply.subs.Bool, index=1, invert=True), \
    Eq[-1].this.rhs.apply(Algebra.Imply.subs.Bool, index=1, invert=True)

    Eq <<= Eq[-2].this.lhs.args[0].lhs.simplify(), Eq[-1].this.rhs.lhs.simplify()

    Eq <<= Eq[-2].this.lhs.args[0].apply(Algebra.Imply.equ.All, wrt=x), \
    Eq[-1].this.rhs.apply(Algebra.Imply.equ.All, wrt=x)




if __name__ == '__main__':
    run()

# created on 2021-01-26
# updated on 2023-04-29
