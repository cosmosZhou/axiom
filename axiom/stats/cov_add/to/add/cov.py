from util import *


@apply
def apply(self, deep=False):
    lhs, rhs = self.of(Covariance)
    if lhs.is_Add:
        if rhs.is_Add and deep:
            sgm = []
            for a in lhs.args:
                for b in rhs.args:
                    if a == b:
                        sgm.append(Variance(a))
                    else:
                        sgm.append(Covariance(a, b))
            rhs = Add(*sgm)
        else:
            rhs = Add(*(Covariance(arg, rhs) for arg in lhs.args))
    elif rhs.is_Add:
        rhs = Add(*(Covariance(lhs, arg) for arg in rhs.args))
    else: 
        return
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Covariance(x, y + z))

    Eq << Eq[0].this.lhs.apply(stats.cov.to.sub.expect)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Covariance).apply(stats.cov.to.sub.expect)

    Eq << Eq[-1].this.find(Covariance).apply(stats.cov.to.sub.expect)

    


if __name__ == '__main__':
    run()
# created on 2023-04-19
