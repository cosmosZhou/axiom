from util import *


@apply
def apply(imply):
    assert imply.expr.is_And

    limits_dict = imply.limits_dict
    for i, eq in enumerate(imply.expr.args):
        if eq.is_Equal:
            if eq.lhs in limits_dict:
                old, new = eq.args
            elif eq.rhs in limits_dict:
                new, old = eq.args
            else:
                continue

            limits = imply.limits_delete(old)
            if any(limit._has(old) for limit in limits):
                continue

            eqs = [*imply.expr.args]
            del eqs[i]
            eqs = [eq._subs(old, new) for eq in eqs]

            domain = limits_dict[old]
            if isinstance(domain, list):
                limit = (old,)
            else:
                limit = (old, domain)
            eq = imply.func(eq, limit).simplify()
            eqs.append(eq)

            return Any(And(*eqs), *limits)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    i, k = Symbol(integer=True)
    j = Symbol(domain=Range(k))
    x = Symbol(real=True, shape=(oo,))
    f, g = Function(shape=(), integer=True)
    f_quote = Function("f'", shape=(), integer=True)
    Eq << apply(Any[x[:n]:f(x[:n]) > 0, i:k]((g(i) > f_quote(j, x[:n])) & Equal(i, j)))

    Eq << Eq[-1].this.expr.apply(algebra.cond.imply.any.et, wrt=j)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.delta, delta=False, simplify=None, ret=0)

    Eq << algebra.any.imply.any.limits.swap.apply(Eq[-1], simplify=None)

    Eq << Eq[0].this.expr.apply(algebra.eq.cond.given.et.subs, simplify=None)





if __name__ == '__main__':
    run()

# created on 2019-02-27
# updated on 2023-06-22
