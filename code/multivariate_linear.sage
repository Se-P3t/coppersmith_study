# -*- coding: utf-8 -*-

load('util.sage')


def herrmann_may_linear_mod(pol, *, X_, m = None, t = None, **kwds):
    r"""
    Implementation of Herrmann M. and May A.'s Solving Linear Equations Modulo Divisors

    INPUT:

    - ``pol`` -- a multivariate linear modular polynomial with small roots
    - ``X_`` -- list of absolute bound for the roots
    - ``beta`` -- compute a root mod `b` where `b` is a factor of `N` and `b \ge
      N^\beta`. (default: 0.499)
    - ``m`` -- an integer parameter
    - ``t`` -- an integer parameter
    - ``method`` -- the method used to solve multivariate polynomial equaction (default: 'bruteforce')
    - ``**kwds`` -- passed through to method :meth:`Matrix_integer_dense.LLL() <sage.matrix.matrix_integer_dense.Matrix_integer_dense.LLL>`.

    EXAMPLES:

    Two chunks::

        sage: p = getPrime(512)
        sage: q = getPrime(512)
        sage: N = p * q

        sage: kbits = 45
        sage: x0 = p % 2^kbits
        sage: y0 = p >> (512 - kbits)
        sage: p0 = p - 2^(512-kbits)*y0 - x0

        sage: sols = (x0, y0)
        sage: sols
        (190325726931, 26341121496566)

        sage: PR.<x, y> = PolynomialRing(Zmod(N))
        sage: pol = p0 + 2^(512-kbits)*y + x
        sage: ZZ(pol(*sols)) == p
        True

        sage: herrmann_may_linear_mod(pol, X_=[2^kbits, 2^kbits], m=6)
        ((190325726931, 26341121496566),)

    Three chunks::

        sage: kbits = 30
        sage: x0 = p % 2^kbits
        sage: y0 = (p >> 256) % 2^kbits
        sage: z0 = p >> (512 - kbits)
        sage: p0 = p - 2^(512-kbits)*z0 - 2^256*y0 - x0

        sage: sols = (x0, y0, z0)
        sage: sols
        (971074363, 961949388, 1036986313)

        sage: PR.<x,y,z> = PolynomialRing(Zmod(N))
        sage: pol = p0 + 2^(512-kbits)*z + 2^256*y + x
        sage: ZZ(pol(*sols)) == p
        True

        sage: herrmann_may_linear_mod(pol, X_=[2^kbits,2^kbits,2^kbits], m=6, t=1)
        ((971074363, 961949388, 1036986313),)

    REFERENCES:

    Herrmann M., May A. (2008) *Solving Linear Equations Modulo Divisors:
    On Factoring Given Any Bits. In: Pieprzyk J. (eds) Advances in Cryptology
    - ASIACRYPT 2008. ASIACRYPT 2008. Lecture Notes in Computer Science,
    vol 5350. Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/978-3-540-89255-7_25
    """
    from itertools import product

    beta = kwds.get('beta', 0.499)
    method = kwds.get('method', 'bruteforce')

    N = pol.parent().characteristic()
    if N == 0:
        raise ArithmeticError("Input polynomial must be defined over Z/nZ.")

    if any(map(lambda x: x != 1, pol.degrees())):
        raise ArithmeticError("Input polynomial must be linear.")

    n = pol.nvariables()
    if len(X_) != n:
        raise ValueError("param `X_` must have length of `pol.nvariables()`")

    beta = RR(beta)
    if beta <= 0.0 or beta >= 1.0:
        raise ValueError("0.0 < beta < 1.0 not satisfied.")

    a0 = pol.monomial_coefficient(pol.parent().gen(0))
    f = (pol / a0).change_ring(ZZ)
    PR, x_ = f.parent().objgens()

    if m is None:
        warnings.warn("parameter `m` may be too big", DeprecationWarning)

        epsilon = RR(1 - (1-beta)**((n+1)/n) - (n+1)*(1-(1-beta)**(1/n))*(1-beta) -
            RR(log(prod(X_), N)))
        verbose(f"epsilon = {epsilon}", level=1, caller_name='param')

        m = ceil(n * (1/pi * (1-beta)**-0.278465 - beta*ln(1-beta)) / epsilon)
        verbose(f"m = {m}", level=1, caller_name='param')

    if t is None:
        tau = 1 - (1-beta)**(1/n)
        t = ceil(tau * m)
        verbose(f"t = {t}", level=1, caller_name='param')

    monos = []
    polys = []

    x0 = x_[0]
    for k, *i_ in product(srange(m+1), repeat=n):
        if k + sum(i_) > m:
            continue

        mono = PR(prod(x**i for i, x in zip([k]+i_, x_)))
        monos.append(mono)
        if DEBUG:
            verbose(str(mono), level=2, caller_name='add mono')

        g = PR(mono/(x0**k) * f**k * N**max(t-k, 0))
        polys.append(g)
        if DEBUG:
            verbose(f"{mono/(x0**k)} f^{k} N^{max(t-k, 0)}", level=2, caller_name='add poly')

    nrows = len(polys)
    ncols = len(monos)
    verbose(f"dim = ({nrows}, {ncols})", level=1, caller_name='param')

    M = Matrix(ZZ, nrows, ncols)
    for i in srange(M.nrows()):
        for j in srange(M.ncols()):
            M[i, j] = polys[i](*(x*X for x, X in zip(x_, X_))).monomial_coefficient(monos[j])

    verbose('Matrix M', level=3, caller_name='matrix overview')
    matrix_overview(M, level=3)

    B = M.LLL(**kwds)

    verbose('Matrix B', level=3, caller_name='matrix overview')
    matrix_overview(B, level=3)

    v = vector([(mono)(*(x/X for x, X in zip(x_, X_))) for mono in monos])
    hs = [PR(row*v) for row in B]

    if DEBUG:
        for i, h in enumerate(hs):
            print(i, h(*sols) == 0)

        __import__('IPython').embed()

    if method == 'resultant':
        potential_roots = solve_hs_resultant(hs[:n])
    elif method == 'bruteforce':
        potential_roots = solve_hs_bruteforce(hs[:-1], max(map(lambda x: ZZ(x).nbits(), X_)))
    else:
        raise RuntimeError(f"unknown method `{method}`")

    roots = set()
    for root in potential_roots:
        if any(map(lambda x: x[0] >= x[1], zip(root, X_))):
            continue
        if gcd(ZZ(pol(*root)), N) > N**beta:
            roots.add(root)

    return tuple(roots)
