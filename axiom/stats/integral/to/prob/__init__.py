from util import *


def compute_probability(condition, *limits):
    var2sym = {}
    sym2var = {}
    if condition.is_Equal:
        conds = [condition]
    else:
        conds = condition.of(And)

    for eq in conds:
        x, x_var = eq.of(Equal)
        var2sym[x] = x_var
        sym2var[x_var] = x

    cond = S.true
    for x, *ab in limits:
        if ab:
            if len(ab) == 2:
                a, b = ab
                assert a < b
                cond &= (sym2var[x] >= a) & (sym2var[x] <= b)
            else:
                return
        else:
            return

    return Probability(cond)


@apply
def apply(self):
    condition, *limits = self.of(Integral[Probability])
    return Equal(self, compute_probability(condition, *limits))


@prove
def prove(Eq):
    from axiom import stats, calculus

    x, y = Symbol(real=True, random=True)
    a, b = Symbol(real=True)
    Eq << apply(Integral[x.var:a:oo, y.var:-oo:b](Probability(x, y)))

    Eq << Eq[0].this.rhs.apply(stats.prob.to.integral)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.limits.swap)


if __name__ == '__main__':
    run()
# created on 2023-04-18


from . import marginal
# updated on 2023-05-20