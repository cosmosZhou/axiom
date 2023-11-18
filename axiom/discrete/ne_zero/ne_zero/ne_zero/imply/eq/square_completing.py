from util import *


@apply
def apply(ne_zero_A, ne_zero_B, ne_zero, self):
    A, S[A] = ne_zero_A.of(Unequal[Det[Expr + Transpose], 0])
    B, S[B] = ne_zero_B.of(Unequal[Det[Expr + Transpose], 0])
    S[A], S[B], S[A], S[B] = ne_zero.of(Unequal[Det[Expr + Expr + Transpose + Transpose], 0])
    ((x, y), A, S[x - y]), ((S[x], z), B, S[x - z]) = self.of((Expr - Expr) @ Expr @ Expr + (Expr - Expr) @ Expr @ Expr)
    
    h = ((A + B + A.T + B.T) ^ -1) @ ((A + A.T) @ y + (B + B.T) @ z)
    k = (y - z) @ ((((A + A.T) ^ -1) + ((B + B.T) ^ -1)) ^ -1) @ (y - z) / 2
    return Equal(self, (x - h) @ (A + B) @ (x - h) + k)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(r"\vec x", real=True, shape=(n,))
    y = Symbol(r"\vec y", real=True, shape=(n,))
    z = Symbol(r"\vec z", real=True, shape=(n,))
    A = Symbol(r"\boldsymbol A", real=True, shape=(n, n))
    B = Symbol(r"\boldsymbol B", real=True, shape=(n, n))
    Eq << apply(Unequal(Det(A + A.T), 0), Unequal(Det(B + B.T), 0), Unequal(Det(A + A.T + B + B.T), 0), (x - y) @ A @ (x - y) + (x - z) @ B @ (x - z))

    P = Symbol(Eq[-1].lhs)
    Eq << P.this.definition

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.add)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(discrete.matmul.to.add, simplify=None)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(discrete.matmul.to.add)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(discrete.matmul.to.add)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(discrete.matmul.to.add)

    Eq << Eq[-1].this.rhs.find(MatMul[Add]).apply(discrete.matmul.to.add)

    Eq << Eq[-1].this.rhs.args[:2].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.args[-3].T

    Eq << Eq[-1].this.rhs.args[3].T

    Eq << Eq[-1].this.rhs.args[3:5].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.find(MatMul[Add[-Expr, -Expr]]).apply(discrete.matmul.to.neg)

    Eq << Eq[-1].this.rhs.args[-2:].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.find(MatMul[Add[-Expr, -Expr]]).apply(discrete.matmul.to.neg)

    Eq << Eq[-1].this.rhs.args[-2:].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.find(MatMul[Add[-Expr, -Expr]]).apply(discrete.matmul.to.neg)

    Eq << discrete.ne_zero.imply.eq.square_completing.apply(Eq[2], Eq[-1].rhs)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(MatMul[Add[-MatMul, -MatMul]]).apply(discrete.matmul.to.neg)

    Eq << Eq[-1].this.find(MatMul[Add[-MatMul, -MatMul]]).apply(discrete.matmul.to.neg)

    Eq << Eq[-1].rhs.args[2].find(Add[MatMul[Add]]).this.args[0].T

    Eq << Eq[-1].this.rhs.args[0].T

    Eq << Eq[-3].subs(Eq[-1])

    Eq.eq = algebra.eq.imply.eq.transport.apply(Eq[-1], rhs=2)

    W = Symbol(Eq.eq.rhs)
    Eq << W.this.definition

    Eq << Eq[-1].this.find(MatMul[Add[-MatMul, -MatMul]]).apply(discrete.matmul.to.neg)

    Eq << Eq[-1].this.find(MatMul[Add[-MatMul, -MatMul]]).apply(discrete.matmul.to.neg, 4)

    Eq << Eq[-1].this.find(MatMul[Add]).apply(discrete.matmul.to.add)

    Eq << Eq[-1].this.find(MatMul[Add]).apply(discrete.matmul.to.add, 5)

    Eq << Eq[-1].this.find(MatMul[Add]).apply(discrete.matmul.to.add, 5)

    #combine y square terms
    Eq << Eq[-1].this.rhs.args[0:4:2].apply(discrete.add.to.matmul)

    #combine z square terms
    Eq << Eq[-1].this.rhs.args[::4].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.args[-1].T

    Eq << Eq[-1].this.rhs.args[-2:].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.args[-1].apply(discrete.matmul.to.neg, 3)

    Eq << Eq[-1].T

    Eq << Eq[-1].this.rhs.args[-1].T

    Eq << Eq[-1] + Eq[-3]

    Eq << Eq[-1].this.rhs.args[:2].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.args[1:3].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.args[0].args[1].args[1:3:].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.args[0].args[1].args[1].apply(discrete.matmul.to.mul, 2)

    Eq << Eq[-1].this.rhs.args[1].args[1].args[1:3:].apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.rhs.args[1].args[1].args[1].apply(discrete.matmul.to.mul, 2)

    Eq << Eq[-1].this.rhs.args[0].args[1].args[1].args[1].args[-2:].apply(discrete.matmul.to.sub)

    Eq << Eq[-1].this.rhs.args[0].find(MatMul[Add]).apply(discrete.matmul.to.add, 1)

    Eq << Eq[-1].this.rhs.args[0].args[1].args[1].args[1].args[-2:].apply(discrete.matmul.to.sub)

    Eq << Eq[-1].this.rhs.args[0].find(MatMul[Add]).apply(discrete.matmul.to.add, 1)

    Eq << Eq[-1].this.rhs.args[1].T

    Eq << discrete.ne_zero.ne_zero.ne_zero.imply.eq.inverse.apply(*Eq[:3])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[-1])

    Eq << discrete.ne_zero.imply.eq.square_completing.apply(Eq[-1], Eq[-2].rhs)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1] / 2

    Eq << Eq.eq.subs(W.this.definition.reversed)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])

    Eq << algebra.eq.imply.eq.transport.apply(Eq[-1], lhs=-1)

    Eq << Eq[-1].this.lhs.definition

    #https://en.wikipedia.org/wiki/Normal_distribution#Vector_form
    
    


if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-05-19
