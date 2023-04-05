from util import *


@apply
def apply(given, index=-1):
    eqs = given.of(Unequal[Probability[And], 0])

    if eqs[-1].is_Tuple:
        eqs, *weights = eqs
    else:
        weights = []
        
    if isinstance(index, slice):
        lhs = And(*eqs[index])
        s = {*range(0 if index.start is None else index.start, len(eqs) if index.stop is None else index.stop, 1 if index.step is None else index.step)}

        rhs = []

        for i in range(len(eqs)):
            if i in s:
                continue
            rhs.append(eqs[i])
        rhs = And(*rhs)
    else:
        lhs = And(*eqs[:index])
        rhs = And(*eqs[index:])
    return Unequal(Probability(lhs, *weights), 0), Unequal(Probability(rhs, *weights), 0)


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x, y), 0))

    _x = pspace(x).symbol
    Eq.x_marginal_probability = stats.integral.to.prob.apply(Integral[_x](Probability(x, y)))

    _y = pspace(y).symbol
    Eq.y_marginal_probability = stats.integral.to.prob.apply(Integral[_y](Probability(x, y)))

    Eq << stats.ne_zero.imply.gt_zero.apply(Eq[0])

    Eq <<= calculus.gt.imply.gt.integral.apply(Eq[-1], (_y,)), \
        calculus.gt.imply.gt.integral.apply(Eq[-1], (_x,))

    Eq <<= Eq[-2].subs(Eq.y_marginal_probability), Eq[-1].subs(Eq.x_marginal_probability)

    Eq <<= algebra.gt.imply.ne.apply(Eq[-1]), algebra.gt.imply.ne.apply(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-12-08
