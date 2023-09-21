from util.search import read_all_py, axiom_directory
from run import project_directory

from std.file import Text
import re

    
def test():
    for py in read_all_py(project_directory()):
        print(py)
        with open(py, 'r') as file:
            text = file.read()
            print(text)
            break

def sparsemax(z):
    import numpy as np
    z_sorted = sorted(z, reverse=True)
    k = np.arange(len(z))
    k_array = 1 + k * z_sorted
    z_cumsum = np.cumsum(z_sorted) - z_sorted
    k_selected = k_array > z_cumsum
    k_max = np.where(k_selected)[0].max()
    threshold = (z_cumsum[k_max] - 1) / (k_max + 1)
    return np.maximum(z - threshold, 0)

def delete_duplicate():
    
    for py in read_all_py(axiom_directory()):
        
        [*lines] = Text(py)
        
        timestamp = {}
        for i, line in enumerate(lines):
            if m := re.match(r' *# *(created|updated) on (\d\d\d\d-\d\d-\d\d)', line):
                timestamp[m[1]] = (i, m[2])
        
        if len(timestamp) == 2:
            if timestamp['created'][1] == timestamp['updated'][1]:
                print('processing', py)
                print(timestamp)
                print('line to be deleted:', timestamp['updated'][0])
                print()
                
                index = timestamp['updated'][0]
                
                del lines[index]
                Text(py).writelines(lines)

def test_select_smaller():
    from sympy import Symbol
    x = Symbol(real=True) 
    a = 1
    b = 2
#     a = b
#     strict inequality test:
    print((x < a) | (x < b))
    print((x < a) | (b > x))
    print((a > x) | (b > x))
    print((a > x) | (x < b))
    
    print((x < b) | (x < a))
    print((b > x) | (x < a))
    print((b > x) | (a > x))
    print((x < b) | (a > x))
    
#     semi-strict inequality test:
    print((x <= a) | (x < b))
    print((x <= a) | (b > x))
    print((a >= x) | (b > x))
    print((a >= x) | (x < b))
    
    print((x < b) | (x <= a))
    print((b > x) | (x <= a))
    print((b > x) | (a >= x))
    print((x < b) | (a >= x))
#     semi-strict inequality test:    
    print((x < a) | (x <= b))
    print((x < a) | (b >= x))
    print((a > x) | (b >= x))
    print((a > x) | (x <= b))
    
    print((x <= b) | (x < a))
    print((b >= x) | (x < a))
    print((b >= x) | (a > x))
    print((x <= b) | (a > x))
    
#     non-strict inequality test:    
    print((x <= a) | (x <= b))
    print((x <= a) | (b >= x))
    print((a >= x) | (b >= x))
    print((a >= x) | (x <= b))
    
    print((x <= b) | (x <= a))
    print((b >= x) | (x <= a))
    print((b >= x) | (a >= x))
    print((x <= b) | (a >= x))
    
def assert_is_valid(A, B):
    C = A - B
    A = A.toset()
    B = B.toset()
    C = C.toset()
    
    for x in C:
        assert x in A, f"assert {x} in A"
        assert x not in B, f"assert {x} not in B"

    for x in A:
        assert (x in B) ^ (x in C), f"assert ({x} in B) ^ ({x} in C)" 

def test_complement():
    from sympy import Range
    #[n, n) - [n, n)
    assert_is_valid(Range(-100, 100), Range(-10, 10))
    assert_is_valid(Range(-100, 100), Range(-10, 100))
    assert_is_valid(Range(-100, 100), Range(-100, 10))
    
    assert_is_valid(Range(-100, 100), Range(-10, 200))
    assert_is_valid(Range(-100, 100), Range(-200, 10))
    
    assert_is_valid(Range(-100, 100), Range(100, 200))
    assert_is_valid(Range(-100, 100), Range(-200, -100))
    
    assert_is_valid(Range(-100, 100), Range(101, 200))
    assert_is_valid(Range(-100, 100), Range(-200, -101))
    
    #[n, n) - [n, n, -1)
    assert_is_valid(Range(-100, 100), Range(10, -10, -1))
    assert_is_valid(Range(-100, 100), Range(10, -100, -1))
    assert_is_valid(Range(-100, 100), Range(100, -10, -1))
    
    assert_is_valid(Range(-100, 100), Range(10, -200, -1))
    assert_is_valid(Range(-100, 100), Range(200, -10, -1))
    
    assert_is_valid(Range(-100, 100), Range(200, 100, -1))
    assert_is_valid(Range(-100, 100), Range(-100, -200, -1))
    
    assert_is_valid(Range(-100, 100), Range(200, 101, -1))
    assert_is_valid(Range(-100, 100), Range(-101, -200, -1))
    
    #[n, n) - [even, even, 2)
    assert_is_valid(Range(-100, 100), Range(-10, 10, 2))
    assert_is_valid(Range(-100, 100), Range(-10, 100, 2))
    assert_is_valid(Range(-100, 100), Range(-100, 10, 2))
    
    assert_is_valid(Range(-100, 100), Range(-10, 200, 2))
    assert_is_valid(Range(-100, 100), Range(-200, 10, 2))
    
    assert_is_valid(Range(-100, 100), Range(100, 200, 2))
    assert_is_valid(Range(-100, 100), Range(-200, -100, 2))
    
    assert_is_valid(Range(-100, 100), Range(102, 200, 2))
    assert_is_valid(Range(-100, 100), Range(-200, -102, 2))
    
    #[n, n) - [even, odd, 2)
    assert_is_valid(Range(-100, 100), Range(-10, 11, 2))
    assert_is_valid(Range(-100, 100), Range(-10, 101, 2))
    assert_is_valid(Range(-100, 100), Range(-100, 11, 2))
    
    assert_is_valid(Range(-100, 100), Range(-10, 201, 2))
    assert_is_valid(Range(-100, 100), Range(-200, 11, 2))
    
    assert_is_valid(Range(-100, 100), Range(100, 201, 2))
    assert_is_valid(Range(-100, 100), Range(-200, -101, 2))
    
    assert_is_valid(Range(-100, 100), Range(102, 201, 2))
    assert_is_valid(Range(-100, 100), Range(-200, -103, 2))
    
    #[n, n) - [odd, even, 2)
    assert_is_valid(Range(-100, 100), Range(-11, 10, 2))
    assert_is_valid(Range(-100, 100), Range(-11, 100, 2))
    assert_is_valid(Range(-100, 100), Range(-101, 10, 2))
    
    assert_is_valid(Range(-100, 100), Range(-11, 200, 2))
    assert_is_valid(Range(-100, 100), Range(-201, 10, 2))
    
    assert_is_valid(Range(-100, 100), Range(101, 200, 2))
    assert_is_valid(Range(-100, 100), Range(-201, -100, 2))
    
    assert_is_valid(Range(-100, 100), Range(101, 200, 2))
    assert_is_valid(Range(-100, 100), Range(-201, -102, 2))

    #[n, n) - [odd, odd, 2)
    assert_is_valid(Range(-100, 100), Range(-11, 11, 2))
    assert_is_valid(Range(-100, 100), Range(-11, 101, 2))
    assert_is_valid(Range(-100, 100), Range(-101, 11, 2))
    
    assert_is_valid(Range(-100, 100), Range(-11, 201, 2))
    assert_is_valid(Range(-100, 100), Range(-201, 11, 2))
    
    assert_is_valid(Range(-100, 100), Range(101, 201, 2))
    assert_is_valid(Range(-100, 100), Range(-201, -101, 2))
    
    assert_is_valid(Range(-100, 100), Range(101, 201, 2))
    assert_is_valid(Range(-100, 100), Range(-201, -103, 2))
    
    #[n, n) - [even, even, -2)
    assert_is_valid(Range(-100, 100), Range(10, -10, -2))
    assert_is_valid(Range(-100, 100), Range(100, -10, -2))
    assert_is_valid(Range(-100, 100), Range(10, -100, -2))
    
    assert_is_valid(Range(-100, 100), Range(200, -10, -2))
    assert_is_valid(Range(-100, 100), Range(10, -200, -2))
    
    assert_is_valid(Range(-100, 100), Range(200, 100, -2))
    assert_is_valid(Range(-100, 100), Range(-100, -200, -2))

    assert_is_valid(Range(-100, 100), Range(200, 102, -2))
    assert_is_valid(Range(-100, 100), Range(-102, -200, -2))
    
    #[n, n) - [even, odd, -2)
    assert_is_valid(Range(-100, 100), Range(10, -11, -2))
    assert_is_valid(Range(-100, 100), Range(100, -11, -2))
    assert_is_valid(Range(-100, 100), Range(10, -101, -2))
    
    assert_is_valid(Range(-100, 100), Range(200, -11, -2))
    assert_is_valid(Range(-100, 100), Range(10, -201, -2))
    
    assert_is_valid(Range(-100, 100), Range(200, 101, -2))
    assert_is_valid(Range(-100, 100), Range(-100, -201, -2))

    assert_is_valid(Range(-100, 100), Range(200, 103, -2))
    assert_is_valid(Range(-100, 100), Range(-102, -201, -2))
    
    #[n, n) - [odd, even, -2)
    assert_is_valid(Range(-100, 100), Range(11, -10, -2))
    assert_is_valid(Range(-100, 100), Range(101, -10, -2))
    assert_is_valid(Range(-100, 100), Range(11, -100, -2))
    
    assert_is_valid(Range(-100, 100), Range(201, -10, -2))
    assert_is_valid(Range(-100, 100), Range(11, -200, -2))
    
    assert_is_valid(Range(-100, 100), Range(201, 100, -2))
    assert_is_valid(Range(-100, 100), Range(-101, -200, -2))

    assert_is_valid(Range(-100, 100), Range(201, 102, -2))
    assert_is_valid(Range(-100, 100), Range(-101, -200, -2))

    #[n, n) - [odd, odd, -2)
    assert_is_valid(Range(-100, 100), Range(11, -11, -2))
    assert_is_valid(Range(-100, 100), Range(101, -11, -2))
    assert_is_valid(Range(-100, 100), Range(11, -101, -2))
    
    assert_is_valid(Range(-100, 100), Range(201, -11, -2))
    assert_is_valid(Range(-100, 100), Range(11, -201, -2))
    
    assert_is_valid(Range(-100, 100), Range(201, 101, -2))
    assert_is_valid(Range(-100, 100), Range(-101, -201, -2))

    assert_is_valid(Range(-100, 100), Range(201, 103, -2))
    assert_is_valid(Range(-100, 100), Range(-101, -201, -2))

    #[n, n, -1) - [n, n)
    assert_is_valid(Range(100, -100, -1), Range(-10, 10))
    assert_is_valid(Range(100, -100, -1), Range(-10, 100))
    assert_is_valid(Range(100, -100, -1), Range(-100, 10))
    
    assert_is_valid(Range(100, -100, -1), Range(-10, 200))
    assert_is_valid(Range(100, -100, -1), Range(-200, 10))
    
    assert_is_valid(Range(100, -100, -1), Range(100, 200))
    assert_is_valid(Range(100, -100, -1), Range(-200, -100))
    
    assert_is_valid(Range(100, -100, -1), Range(101, 200))
    assert_is_valid(Range(100, -100, -1), Range(-200, -101))
    
    #[n, n, -1) - [n, n, -1)
    assert_is_valid(Range(100, -100, -1), Range(10, -10, -1))
    assert_is_valid(Range(100, -100, -1), Range(10, -100, -1))
    assert_is_valid(Range(100, -100, -1), Range(100, -10, -1))
    
    assert_is_valid(Range(100, -100, -1), Range(10, -200, -1))
    assert_is_valid(Range(100, -100, -1), Range(200, -10, -1))
    
    assert_is_valid(Range(100, -100, -1), Range(200, 100, -1))
    assert_is_valid(Range(100, -100, -1), Range(-100, -200, -1))
    
    assert_is_valid(Range(100, -100, -1), Range(200, 101, -1))
    assert_is_valid(Range(100, -100, -1), Range(-101, -200, -1))
    
    #[n, n, -1) - [even, even, 2)
    assert_is_valid(Range(100, -100, -1), Range(-10, 10, 2))
    assert_is_valid(Range(100, -100, -1), Range(-10, 100, 2))
    assert_is_valid(Range(100, -100, -1), Range(-100, 10, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(-10, 200, 2))
    assert_is_valid(Range(100, -100, -1), Range(-200, 10, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(100, 200, 2))
    assert_is_valid(Range(100, -100, -1), Range(-200, -100, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(102, 200, 2))
    assert_is_valid(Range(100, -100, -1), Range(-200, -102, 2))
    
    #[n, n, -1) - [even, odd, 2)
    assert_is_valid(Range(100, -100, -1), Range(-10, 11, 2))
    assert_is_valid(Range(100, -100, -1), Range(-10, 101, 2))
    assert_is_valid(Range(100, -100, -1), Range(-100, 11, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(-10, 201, 2))
    assert_is_valid(Range(100, -100, -1), Range(-200, 11, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(100, 201, 2))
    assert_is_valid(Range(100, -100, -1), Range(-200, -101, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(102, 201, 2))
    assert_is_valid(Range(100, -100, -1), Range(-200, -103, 2))
    
    #[n, n, -1) - [odd, even, 2)
    assert_is_valid(Range(100, -100, -1), Range(-11, 10, 2))
    assert_is_valid(Range(100, -100, -1), Range(-11, 100, 2))
    assert_is_valid(Range(100, -100, -1), Range(-101, 10, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(-11, 200, 2))
    assert_is_valid(Range(100, -100, -1), Range(-201, 10, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(101, 200, 2))
    assert_is_valid(Range(100, -100, -1), Range(-201, -100, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(101, 200, 2))
    assert_is_valid(Range(100, -100, -1), Range(-201, -102, 2))

    #[n, n, -1) - [odd, odd, 2)
    assert_is_valid(Range(100, -100, -1), Range(-11, 11, 2))
    assert_is_valid(Range(100, -100, -1), Range(-11, 101, 2))
    assert_is_valid(Range(100, -100, -1), Range(-101, 11, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(-11, 201, 2))
    assert_is_valid(Range(100, -100, -1), Range(-201, 11, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(101, 201, 2))
    assert_is_valid(Range(100, -100, -1), Range(-201, -101, 2))
    
    assert_is_valid(Range(100, -100, -1), Range(101, 201, 2))
    assert_is_valid(Range(100, -100, -1), Range(-201, -103, 2))
    
    #[n, n, -1) - [even, even, -2)
    assert_is_valid(Range(100, -100, -1), Range(10, -10, -2))
    assert_is_valid(Range(100, -100, -1), Range(100, -10, -2))
    assert_is_valid(Range(100, -100, -1), Range(10, -100, -2))
    
    assert_is_valid(Range(100, -100, -1), Range(200, -10, -2))
    assert_is_valid(Range(100, -100, -1), Range(10, -200, -2))
    
    assert_is_valid(Range(100, -100, -1), Range(200, 100, -2))
    assert_is_valid(Range(100, -100, -1), Range(-100, -200, -2))

    assert_is_valid(Range(100, -100, -1), Range(200, 102, -2))
    assert_is_valid(Range(100, -100, -1), Range(-102, -200, -2))
    
    #[n, n, -1) - [even, odd, -2)
    assert_is_valid(Range(100, -100, -1), Range(10, -11, -2))
    assert_is_valid(Range(100, -100, -1), Range(100, -11, -2))
    assert_is_valid(Range(100, -100, -1), Range(10, -101, -2))
    
    assert_is_valid(Range(100, -100, -1), Range(200, -11, -2))
    assert_is_valid(Range(100, -100, -1), Range(10, -201, -2))
    
    assert_is_valid(Range(100, -100, -1), Range(200, 101, -2))
    assert_is_valid(Range(100, -100, -1), Range(-100, -201, -2))

    assert_is_valid(Range(100, -100, -1), Range(200, 103, -2))
    assert_is_valid(Range(100, -100, -1), Range(-102, -201, -2))
    
    #[n, n, -1) - [odd, even, -2)
    assert_is_valid(Range(100, -100, -1), Range(11, -10, -2))
    assert_is_valid(Range(100, -100, -1), Range(101, -10, -2))
    assert_is_valid(Range(100, -100, -1), Range(11, -100, -2))
    
    assert_is_valid(Range(100, -100, -1), Range(201, -10, -2))
    assert_is_valid(Range(100, -100, -1), Range(11, -200, -2))
    
    assert_is_valid(Range(100, -100, -1), Range(201, 100, -2))
    assert_is_valid(Range(100, -100, -1), Range(-101, -200, -2))

    assert_is_valid(Range(100, -100, -1), Range(201, 102, -2))
    assert_is_valid(Range(100, -100, -1), Range(-101, -200, -2))

    #[n, n, -1) - [odd, odd, -2)
    assert_is_valid(Range(100, -100, -1), Range(11, -11, -2))
    assert_is_valid(Range(100, -100, -1), Range(101, -11, -2))
    assert_is_valid(Range(100, -100, -1), Range(11, -101, -2))
    
    assert_is_valid(Range(100, -100, -1), Range(201, -11, -2))
    assert_is_valid(Range(100, -100, -1), Range(11, -201, -2))
    
    assert_is_valid(Range(100, -100, -1), Range(201, 101, -2))
    assert_is_valid(Range(100, -100, -1), Range(-101, -201, -2))

    assert_is_valid(Range(100, -100, -1), Range(201, 103, -2))
    assert_is_valid(Range(100, -100, -1), Range(-101, -201, -2))


    #[n, n) - [n, n, 3)
    assert_is_valid(Range(-100, 100), Range(100, 200, 3))
    assert_is_valid(Range(-100, 100), Range(-200, -100, 3))
    
    assert_is_valid(Range(-100, 100), Range(102, 200, 3))
    assert_is_valid(Range(-100, 100), Range(-200, -102, 3))

    #[n, n) - [n, n, -3)
    assert_is_valid(Range(-100, 100), Range(200, 100, -3))
    assert_is_valid(Range(-100, 100), Range(-102, -200, -3))

    assert_is_valid(Range(-100, 100), Range(200, 102, -3))
    assert_is_valid(Range(-100, 100), Range(-102, -200, -3))


    #[n, n, -1) - [n, n, 3)
    assert_is_valid(Range(100, -100, -1), Range(102, 200, 3))
    assert_is_valid(Range(100, -100, -1), Range(-200, -100, 3))
    
    assert_is_valid(Range(100, -100, -1), Range(102, 200, 3))
    assert_is_valid(Range(100, -100, -1), Range(-200, -102, 3))

    #[n, n, -1) - [n, n, -3)
    assert_is_valid(Range(100, -100, -1), Range(200, 100, -3))
    assert_is_valid(Range(100, -100, -1), Range(-100, -200, -3))

    assert_is_valid(Range(100, -100, -1), Range(200, 102, -3))
    assert_is_valid(Range(100, -100, -1), Range(-102, -200, -3))

def test_select_greater():
    from sympy import Symbol
    x = Symbol(real=True) 
    a = 1
    b = 2
    
#     a = b
#     strict inequality test:

    print((x > a) | (x > b))
    print((x > a) | (b < x))
    print((a < x) | (b < x))
    print((a < x) | (x > b))
    
    print((x > b) | (x > a))
    print((b < x) | (x > a))
    print((b < x) | (a < x))
    print((x > b) | (a < x))
    
#     semi-strict inequality test:
    print((x >= a) | (x > b))
    print((x >= a) | (b < x))
    print((a <= x) | (b < x))
    print((a <= x) | (x > b))
    
    print((x > b) | (x >= a))
    print((b < x) | (x >= a))
    print((b < x) | (a <= x))
    print((x > b) | (a <= x))
#     semi-strict inequality test:    
    print((x > a) | (x >= b))
    print((x > a) | (b <= x))
    print((a < x) | (b <= x))
    print((a < x) | (x >= b))
    
    print((x >= b) | (x > a))
    print((b <= x) | (x > a))
    print((b <= x) | (a < x))
    print((x >= b) | (a < x))
    
#     non-strict inequality test:    
    print((x >= a) | (x >= b))
    print((x >= a) | (b <= x))
    print((a <= x) | (b <= x))
    print((a <= x) | (x >= b))
    
    print((x >= b) | (x >= a))
    print((b <= x) | (x >= a))
    print((b <= x) | (a <= x))
    print((x >= b) | (a <= x))
    
def test_sparsemax():    
    z = [0.5, 0.3, 0.1, 0.1, 0, 0.9] * 10
    
    z = sparsemax(z)
    _z = sparsemax(z, False)
    print(sum(z), sum(_z))
    print(z == _z)

def PLU():
#     from sympy import *
    import numpy as np
    n = 7
    X = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            X[i][j] = j ** i
    
    # X[:2] = X[1::-1]
    
    A = Matrix(X)
    P, L, U = A.LUdecomposition()
    
    print('A =', A, sep='\n')
    print('P =', P, sep='\n')
    print('L =', L, sep='\n')
    print('U =', U, sep='\n')
    print('P @ L @ U =', P @ L @ U, sep='\n')
    
    for i in range(n):
        for j in range(n):
            X[i][j] = Stirling(i, j)
    
    L = Matrix(X)
    
    for i in range(n):
        for j in range(n):
            X[i][j] = FallingFactorial(j, i)
    
    U = Matrix(X)
    
    print('L =', L, sep='\n')
    print('U =', U, sep='\n')
    print('L @ U =', L @ U, sep='\n')


if __name__ == '__main__':
    test_complement()
#     test_select_greater()
