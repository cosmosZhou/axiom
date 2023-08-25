from util import *


@apply
def apply(self, pivot=-1, j=None):
    args, (k, i, n) = self.of(Sum[Mul])
    n -= 1
    if not n >= i:
        print(n >= i, 'possibly logic error')
        
    import std
    fk, gk = std.array_split(args, pivot)
    fk = Mul(*fk)
    gk = Mul(*gk)
    if j is None:
        j = self.generate_var(integer=True, excludes={k, n})
    return Equal(self, fk._subs(k, n) * Sum[k:i:n + 1](gk) - Sum[k:i:n]((fk._subs(k, k + 1) - fk) * Sum[j:i:k + 1](gk._subs(k, j))))


@prove
def prove(Eq):
    from axiom import algebra

    i, j, k = Symbol(integer=True)
    f, g = Function(real=True)
    n = Symbol(domain=Range(i, oo))
    Eq << apply(Sum[k:i:n + 1](f(k) * g(k)), j=j)

    Eq << Eq[0].this.lhs.apply(algebra.sum.limits.subs.offset, i)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.by_parts)

    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.limits.subs.offset, -i)

    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.limits.subs.offset, -i)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.subs.offset, -i)

    


if __name__ == '__main__':
    run()
# created on 2023-08-19
