from util import *


@apply
def apply(self, *, cond=None):
    matched = []
    unmatch = []
    for eq in self.of(And):
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert unmatch
    return And(*unmatch), Or(cond, And(*matched))


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c, d = Symbol(integer=True, given=True)
    x, y = Symbol(real=True, given=True)
    f, g = Function(real=True)
    Eq << apply(((a < b) | (c < d)) & (f(x) < g(y)) & ((x < y) | (c < d)), cond=c < d)

    Eq << algebra.ou.imply.et.apply(Eq[-1])

    Eq << algebra.et.given.et.apply(Eq[0])

    Eq << algebra.et.given.et.apply(Eq[-1])

    


if __name__ == '__main__':
    run()

# created on 2019-04-29
# updated on 2023-05-21
