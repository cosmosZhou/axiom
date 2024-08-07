from util import *


@apply
def apply(self, t_p):
    a, W = self.of(Expr @ Expr)
    W = W.T

    hidden_size = a.shape[-1] / t_p
    a = a.split(hidden_size, dim=-1)
    W = W.split(hidden_size, dim=-1)
    i = a.generate_var(integer=True, excludes=a.variables_set | W.variables_set | W.free_symbols)
    return Equal(self, Sum[i:t_p](a[i] @ W[i].T))

@prove
def prove(Eq):
    from axiom import algebra, discrete

    # m denotes batch size
    # n denotes sequence length
    # d denotes hidden size
    # d_o denotes output hidden size
    # t_p denotes tensor parallel
    m, n, d, d_o, t_p = Symbol(integer=True, positive=True)
    # a denotes attention output
    d *= t_p
    a = Symbol(real=True, shape=(m, n, d))
    W = Symbol(real=True, shape=(d_o, d))
    Eq << apply(a @ W.T, t_p)

    k, j = Eq[0].find(Lamda).variables
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)

    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], k)

    i = Symbol(domain=Range(d_o))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum, simplify=None)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.reducedSum)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.reshape, t_p, d / t_p)
    
    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.axes.separate)
    Eq << Eq[-1].this.lhs.arg.apply(algebra.reducedSum.to.lamda, simplify=None)
    Eq << Eq[-1].this.lhs.find(Sum).apply(discrete.sum.to.matmul)
    
    # https://github.com/huggingface/transformers/blob/main/src/transformers/models/llama/modeling_llama.py#L444


if __name__ == '__main__':
    run()
# created on 2023-12-15
# updated on 2023-12-18
