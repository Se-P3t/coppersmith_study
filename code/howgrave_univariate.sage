# -*- coding: utf-8 -*-

load('util.sage')


def howgrave_univariate(pol, *, X, h=None, strict=False, **kwds):
    r"""
    Implementaion of Coppersmith's Solving Univariate Modular Equation with Small Root Revisited by Howgrave-Graham.

    INPUT:

    - ``pol`` -- a monic univariate polynomial with small root
    - ``X`` -- an absolute bound for the root
    - ``h`` -- an integer parameter
    - ``strict`` -- (bool) ``True`` for checking the parameter `X` and the bound of roots
    - ``**kwds`` -- passed through to method :meth:`Matrix_integer_dense.LLL() <sage.matrix.matrix_integer_dense.Matrix_integer_dense.LLL>`.

    EXAMPLES:

    We examine the approach by solving the example used in Sec.4::

        sage: N = 35
        sage: F = Zmod(N)
        sage: PR = PolynomialRing(F, 'x')
        sage: x = PR.gen()
        sage: pol = x^2 + 14*x + 19

        sage: howgrave_univariate(pol, X=4, h=3, strict=True)
        [4]

    Note that this method will still find the solution even though `x_0 > X`::

        sage: howgrave_univariate(pol, X=2, h=3, strict=False)
        [3]

    Next, we compare it with ``small_roots``::

        sage: p = getPrime(1024)
        sage: q = getPrime(1024)
        sage: N = p*q
        sage: m = getRandomNBitInteger(2000)
        sage: c = power_mod(m, 3, N)

        sage: F = Zmod(N)
        sage: PR = PolynomialRing(F, 'x')
        sage: x = PR.gen()
        sage: nbits = 600
        sage: x0 = m % (1<<nbits)
        sage: pol = (x + m - x0)**3 - c
        sage: x0
        3655827715...54686973659

        sage: pol.small_roots(X=1<<nbits)
        []
        sage: howgrave_univariate(pol, X=1<<nbits, h=6)
        [36558277155...4686973659]

    REFERENCES:

    N. Howgrave-Graham. *Finding small roots of univariate modular equations
    revisited.* In M. Darnell, editor, IMA Int. Conf., volume 1355 of
    Lecture Notes in Computer Science, pages 131–142. Springer, 1997.
    https://doi.org/10.1007/BFb0024458
    """
    if not pol.is_monic():
        raise ArithmeticError("Polynomial must be monic.")

    if h < 2:
        raise ValueError("h is too small, at least 2")

    N = pol.parent().characteristic()

    f = pol.change_ring(ZZ)

    PR, (x,) = f.parent().objgens()

    k = f.degree()

    epsilon = RR(1 / log(N, 2))
    verbose(f"epsilon = {epsilon}", level=1, caller_name='param')

    hh = ceil(max(RR(7 / k), RR((k+epsilon*k-1) / (epsilon*k**2))))
    if h is not None:
        if h < hh:
            verbose("h is small, may not find a solution", level=2, caller_name='param check')
    else:
        h = hh
        verbose(f"h = {h}", level=1, caller_name='param')

    if strict and X >= ((4/3)**(-1/2) * (h*k)**(-1/(h*k-1))) * N**((h-1)/(h*k-1)):
        raise ValueError("Theoretically unsolvable.")

    quv = {}
    for i in srange(h*k):
        v = i // k
        u = i - k*v
        quv[u, v] = N**(h-1-v) * x**u * f**v

    M = Matrix(ZZ, h*k)
    for i in srange(h*k):
        for j in srange(h*k):
            v = i // k
            u = i - k*v
            M[i, j] = quv[u, v].monomial_coefficient(x**j) * X**j

    verbose('Matrix M', level=3, caller_name='matrix overview')
    matrix_overview(M, level=3)

    B = M.LLL(**kwds)

    verbose('Matrix B', level=3, caller_name='matrix overview')
    matrix_overview(B, level=3)

    poly_sol = PR([(e / X**i) for i, e in enumerate(B[0])])

    roots = [ZZ(rt[0]) for rt in poly_sol.roots() if pol(ZZ(rt[0])) == 0]
    if strict:
        roots = [x0 for x0 in roots if abs(x0) <= X]

    if DEBUG:
        __import__('IPython').embed()

    return roots
