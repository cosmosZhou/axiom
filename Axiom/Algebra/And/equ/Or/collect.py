from util import *


@apply
def apply(self, *, cond=None):
    cond=sympify(cond)

    matched = []
    unmatch = []
    for eq in self.args:
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert not unmatch
    return Or(cond, self.func(*matched))


@prove
def prove(Eq):
    from Axiom import Algebra

    p, q, r, s = Symbol(bool=True)
    Eq << apply(And(q | p, r | p, s | p), cond=p)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.to.Or.collect, cond=p)

    Eq << Eq[-1].this.lhs.apply(Algebra.And.of.Or.collect, cond=p)




if __name__ == '__main__':
    run()
# created on 2022-01-28