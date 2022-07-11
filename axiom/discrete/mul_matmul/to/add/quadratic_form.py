from util import *


def quadratic_form(x, c, doit=True):
    from axiom.discrete.matmul.to.matrix import list_to_tuple
    [n] = x.shape
    if doit:
        mat = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if i != j:
                    mat[i][j] = c[2 ** i + 2 ** j]
        A = Matrix(list_to_tuple(mat))
    else:
        i = x.generate_var(c.free_symbols, integer=True)
        j = x.generate_var(c.free_symbols | {i}, integer=True)
        A = Lamda[j:n, i:n](Bool(Unequal(j, i)) * c[2 ** i + 2 ** j])
                
    return x @ A @ x / 2
    
def reduced_sum(x, c):
    from axiom.algebra.mul.to.add.poly import generate_combination
    [n] = x.shape
    sgm = 0
    for a, b in generate_combination(n, 2):
        sgm += c[2 ** a + 2 ** b] * x[a] * x[b]
        
    return sgm
        
@apply
def apply(self):    
    x, mat, S[x] = self.of(MatMul / 2)
    [n] = x.shape
    assert mat.is_Matrix
    
    coefficient = None
    for i in range(n):
        for j in range(n):
            if i != j: 
                c, index = mat[i][j].of(Indexed)
                assert index == 2 ** i + 2 ** j
                
                if coefficient is None:
                    coefficient = c
                else:
                    assert coefficient == c
          
    return Equal(self, reduced_sum(x, c))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = 5
    x = Symbol(real=True, shape=(n,))
    a = Symbol(real=True, shape=(2 ** n,))
    Eq << apply(quadratic_form(x, a))

    Eq << Eq[-1].find(Symbol).this.apply(algebra.expr.to.matrix)

    Eq << Eq[0].subs(Eq[-1])

    Eq << MatMul(*Eq[-1].find(MatMul).args[:2]).this.apply(discrete.matmul.to.matrix)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.matrix)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    
    


if __name__ == '__main__':
    run()
# created on 2021-12-24
# updated on 2022-03-16
