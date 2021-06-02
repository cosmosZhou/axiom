from util import *



def sigma(x, *limits):
    n = x.shape[0]
    (k,), *_ = limits
    i = x.generate_var(exclues=k, integer=True, var='i')
    j = x.generate_var(exclues={k, i}, integer=True, var='j')    
    d = x.generate_var(exclues={k, i, j}, shape=(oo,), integer=True, var='d')

    return Piecewise((ZeroMatrix(*x.shape[1:]), Equal(k, 0) | (k > n)),
                     (Sum[d[:k]:ForAll[j:i, i:k](d[j] < d[i]):CartesianSpace(Range(0, n), k)](abs(Product[i:k](x[d[i]]))), True))


sigma = Function.sigma(eval=sigma, shape=())

    
@apply
def apply(self):
    assert self.is_sigma
    x, (k,) = self.args
    n = x.shape[0]
    assert k >= 2
    n -= 1
    return Equal(self, x[n] * sigma[k - 1](x[:n]) + sigma[k](x[:n]))


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(oo,))
    k = Symbol.k(domain=Range(2, n + 1))
    
    Eq << apply(sigma[k](x[:n + 1]))
    
    Eq << Eq[-1].this.find(sigma).defun()
    
    Eq << Eq[-1].this.find(sigma).defun()
    
    Eq << Eq[-1].this.find(sigma).defun()

    
if __name__ == '__main__':
    run()

from . import two
