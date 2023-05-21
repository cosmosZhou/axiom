from util import *


@apply
def apply(self):
    x = self.of(Adjoint)
    assert not x.shape
    return Equal(self, ~x)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(Adjoint(x))

    


if __name__ == '__main__':
    run()
# created on 2023-05-01
