from util import *


@apply
def apply(self, diff=-1):
    [*array] = self.of(Mul)
    for i, expr in enumerate(array):
        if args := expr.of(KroneckerDelta):
            x, y = args
            index = i + diff
            if i == index:
                if i + 1 < len(array):
                    index = i + 1
                elif i - 1 >= 0:
                    index = i - 1
                else:
                    return
                
            ret = array[index].subs(x, y)
            if ret == array[index]:
                ret = array[index].subs(y, x)
                
            array[index] = ret
            break
        
    return Equal(self, Mul(*array), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    f = Function(complex=True)
    Eq << apply(f(y) * f(x) * KroneckerDelta(x, y))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.kroneckerDelta.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.piece)

    


if __name__ == '__main__':
    run()
# created on 2023-03-17
