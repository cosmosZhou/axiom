from util import *

def trim_leading(shape):
    while shape:
        if shape[0] == 1:
            shape = shape[1:]
        else:
            break

    return shape
        
def split(self, *pivot, axis=0):
    rhs = self
    shape = self.shape
    for k in pivot:
        if k < 0:
            k += shape[axis]
            
        former = rhs[tuple([slice(None, None)] * axis + [slice(0, k)])]
        latter = rhs[tuple([slice(None, None)] * axis + [slice(k, shape[axis])])]
        assert former.shape == trim_leading(shape[:axis] + (k,) + shape[axis + 1:])
        assert latter.shape == trim_leading(shape[:axis] + (shape[axis] - k,) + shape[axis + 1:])
        rhs = BlockMatrix[axis](former, latter, shape=shape)

        assert rhs.shape == shape
        axis += 1
    
    return rhs

@apply
def apply(self, *pivot, axis=0):
    return Equal(self, split(self, *pivot, axis=axis), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    m = Symbol(integer=True, positive=True)
    A = Identity(m)
    A = Symbol(real=True, shape=(m, m, m, m, m))
    i, j = Symbol(domain=Range(1, m))
    Eq << apply(A, i, j, axis=2)

    t = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], t)

    k = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], k)

    l = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], l)

    p = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], p)





if __name__ == '__main__':
    run()
# created on 2023-03-31
# updated on 2023-04-29

