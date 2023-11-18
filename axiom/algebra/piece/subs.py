from util import *

def subs(self, index, reverse):
    expr, cond = self.args[index]
    if cond.is_And:
        for eq in cond.args:
            if eq.is_Equal:
                break
        else:
            return
    else:
        eq = cond

    lhs, rhs = eq.of(Equal)
    if reverse:
        lhs, rhs = rhs, lhs
        expr = expr._subs(lhs, rhs)
    else:
        _expr = expr._subs(lhs, rhs)
        if _expr == expr:
            expr = expr._subs(rhs, lhs)
        else:
            expr = _expr
    ec = [*self.args]
    ec[index] = (expr, cond)
    return self.func(*ec)

@apply
def apply(self, index=None, reverse=False):
    if index is None:
        for index, (expr, cond) in enumerate(self.args):
            if cond.is_Equal:
                break
        else:
            for index, (expr, cond) in enumerate(self.args):
                if cond.is_And:
                    break
            else:
                return

    if isinstance(index, (tuple, list)):
        rhs = self
        for index in index:
            rhs = subs(rhs, index, reverse)
    else:
        rhs = subs(self, index, reverse)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,))
    A = Symbol(etype=dtype.real[k])
    g, f, h = Function(shape=(), real=True)
    Eq << apply(Piecewise((g(x), Equal(x, y) & (h(y) > 0)), (f(x), Element(y, A)), (h(x), True)))

    p = Symbol(Eq[0].lhs)
    Eq << p.this.definition

    Eq << algebra.cond_piece.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].args[:2].apply(algebra.eq.cond.imply.cond.subs, ret=0)

    Eq << algebra.ou.imply.eq.piece.apply(Eq[-1], wrt=p)

    Eq << Eq[0].this.rhs.apply(algebra.piece.et.invert)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[1], Eq[-2])

    
    


if __name__ == '__main__':
    run()

# created on 2018-02-04
# updated on 2023-11-11
