from sympy import *
from sympy import Rational as sr
from sympy import simplify as simplif

sim_memo = {}
def simplify(a):
    if a in sim_memo:
        return sim_memo[a]
    else:
        x = simplif(a)
        sim_memo[a] = x
        return x

stir1_memo = {}
def stir1(n, k): #calcula el número de stirling de primer tipo
    if n < 0 or k < 0 or k > n:
        return 0
    elif n == 0 and k == 0:
        return 1
    else:
        if (n, k) in stir1_memo:
            return stir1_memo[n, k]
        else:
            a = (n - 1) * stir1(n - 1, k) + stir1(n - 1, k - 1)
            stir1_memo[n, k] = a
            return a

stir2_memo = {}
def stir2(n, k): #calcula el número de stirling de segundo tipo
    n1 = n
    k1 = k
    if n < 0 or k < 0 or k > n:
        return 0
    elif n == 0 and k == 0:
        return 1
    else:
        if (n, k) in stir2_memo:
            return stir2_memo[n, k]
        temp1 = stir2(n1 - 1, k1)
        temp1 = k1 * temp1
        h = (k1 * (stir2(n1 - 1, k1))) + stir2(n1 - 1, k1 - 1)
        stir2_memo[n, k] = h
        return h


comb_memo = {}
def comb(n, k): #calcula el número combinatorio entre n y k
    if n < 0 or k < 0 or k > n:
        return 0
    elif n == 0 and k == 0:
        return 1
    else:
        if (n, k) in comb_memo:
            return comb_memo[n, k]
        h = comb(n - 1, k) + comb(n - 1, k - 1)
        comb_memo[n, k] = h
        return h


def coef(m):
    return [sum([sr(1, i) * stir2(m, i-1) * sum([stir1(i, j) * comb(j, s) * (-1) ** (i+j) for j in range(s, i+1)]) for i in range(s, m+2)]) for s in range(1, m+2)]


def lam(A):
    n = len(A)
    B = [simplify(A[i]) for i in range(n)]
    return [1 / (prod([B[j] - B[i] for j in range(i)]) * prod([B[j] - B[i] for j in range(i+1, n)])) for i in range(n)]

H_memo = {}
def H(k, m=1): #Devuelve el número armónico generalizado H_k^(m)
    if m == 1:
        if k in H_memo:
            return H_memo[k]
        if isinstance(k, int):
            if k < 0:
                return 'indefinido'
            h = sum([sr(1, (i**m)) for i in range(1, k+1)])
            H_memo[k] = h
            return h
        if isinstance(k, sr):
            p, q = k.as_numer_denom()
            if q == 1:
                p = int(p)
                return H(p)
            if k > 0 and p < q:
                x = simplify(q/p -(pi/2) * cot(p*pi/q)-log(q)+sum([cos(2*s*p*pi/q)*log(2*sin(s*pi/q)) for s in range(1, q)]))
                H_memo[k] = x
                return x
            if k < 0 and p < q:
                x = simplify(H(-k) + 1/k +pi*cot(pi *(-k)))
                H_memo[k] = x
                return x
            if p > q:
                x = simplify(H(k-1) + 1/k)
                H_memo[k] = x
                return x
        else:
            return harmonic(k, m)
    else:
        if isinstance(k, int):
            if k < 0:
                return 'indefinido'
        if isinstance(k, sr):
            p, q = k.as_numer_denom()
            if q == 1:
                p = int(p)
                return H(p, m)
        return harmonic(k, m)


def evalsumsqf(A, B):
    n = len(B)
    m = len(A)
    if n < m+1:
        return 'la suma no converge'
    L = lam(B)
    return simplify(sum([(-1)**(i+1) * A[i]*sum([L[j] * B[j]**i * H(B[j]) for j in range(n)]) for i in range(m)]))

def fracpar(A, B):
    n = len(B)
    m = len(A)
    if A[m-1] == 0:
        return 'coeficiente principal nulo'
    if sum([B[j][1] for j in range(n)]) <= m-1:
        return 'la función racional dada no es propia'
    z = Symbol('z')
    s = [[Symbol('x{}{}'.format(i, j)) for j in range(B[i][1])] for i in range(n)]
    f = sum([sum([s[i][j]/(z+B[i][0])**(j+1) for j in range(B[i][1])]) for i in range(n)])
    g = sum([A[i] * z**i for i in range(m)])/prod([(z+B[i][0])**B[i][1] for i in range(n)])
    eq = Eq(f, g)
    S = solve_undetermined_coeffs(eq, [s[i][j] for i in range(n) for j in range(B[i][1])], z)
    return [[S[s[i][j]] for j in range(B[i][1])] for i in range(n)]

def evalsum(A, B):
    n = len(B)
    m = len(A)
    if A[m - 1] == 0:
        return 'coeficiente principal nulo'
    if sum([B[j][1] for j in range(n)]) < m +1:
        return 'la suma no converge'
    S = fracpar(A, B)
    return simplify(sum([sum([S[i][j]*(zeta(j+1) - H(B[i][0], j+1)) for j in range(1, B[i][1])]) for i in range(n)]) -
                    sum([S[i][0]*H(B[i][0]) for i in range(n)]))

#Algoritmos para comprobar cosas:


def f(k, n): #calcula la potencia de factorial descendiente k^n_ en términos de las potencias usuales con la fórmula que involucra los números de stirling de primer tipo
    return sum([stir1(n, i) * (-1) ** (n + i) * k ** i for i in range(0, n + 1)])

def des(k, n): #calcula la potencia de factorial descendiente k^n_
    return prod([k-i for i in range(0, n)])

def sum1(n, m): # suma 0 ** m + 1 ** m + 2 ** m + ... + n ** m acapella
    return sum([i ** m for i in range(1, n+1)])

def sum2(n, m): # suma 0 ** m + 1 ** m + 2 ** m + ... + n ** m usando la formula deducida usando calculo finito
    a = coef(m)
    return sum([(a[i][0] / a[i][1]) * n ** (i+1) for i in range(0, m+1)])

def blag(A, x):
    n = len(A)
    return [prod([(x-A[i]) / (A[j] - A[i]) for i in range(j)]) * prod([(x-A[i]) / (A[j] - A[i]) for i in range(j+1, n)]) for j in range(n)]





