from util import *


@apply
def apply(self, i=None, j=None):
    A = self.of(Det)
#         https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
    n = A.shape[0]
    if i is None:
        j = sympify(j)
        i = A.generate_var(excludes=j.free_symbols, integer=True)
        sigmar = Sum[i:n]
    else:
        i = sympify(i)
        j = A.generate_var(excludes=i.free_symbols, integer=True)
        sigmar = Sum[j:n]

    return Equal(self, sigmar(A[i, j] * Cofactors(A)[i, j]).simplify())


@prove(slow=True)
def prove(Eq):
    from axiom import algebra

    print('this is a validation, not a proof in', __file__)
    n, i = Symbol(integer=True, positive=True)
    n = 5
    i = 4
    A = Symbol(shape=(n, n), complex=True, zero=False)
    Eq << apply(det(A), i=i)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.doit)

    Eq << Eq[-1].this.rhs.args[0].args[1].arg.apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.args[1].args[2].arg.apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.args[2].args[1].arg.apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.args[3].args[2].arg.apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.args[4].args[1].arg.apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.lhs.arg.apply(algebra.expr.to.lamda)

    Eq << Eq[-1].this.lhs.arg.apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].doit(deep=True)

    Eq << Eq[-1].this.rhs.expand()

    
    


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
# created on 2020-08-17
# updated on 2021-11-21