# -*- coding: utf-8 -*-

load('util.sage')


def coron_bivariate(pol, *, X, Y, k=None, check_all=False, **kwds):
    """
    Implementation of Coron's Solving Bivariate Integer Polynomial Equactions

    INPUT:

    - ``pol`` -- a bivariate polynomial with small roots over integers
    - ``X`` -- an absolute bound for the root of `x`
    - ``Y`` -- an absolute bound for the root of `y`
    - ``k`` -- an integer parameter
    - ``check_all`` -- (bool) ``True`` for checking all reduced polynomial `h`
    - ``**kwds`` -- passed through to method :meth:`Matrix_integer_dense.LLL() <sage.matrix.matrix_integer_dense.Matrix_integer_dense.LLL>`.

    EXAMPLES::

        sage: p = getPrime(256)
        sage: q = getPrime(256)
        sage: N = p * q
        sage: x0 = p % 2**112
        sage: y0 = q % 2**112
        sage: p0 = p - x0
        sage: q0 = q - y0
        sage: x0, y0
        (3330293348008139537089436726746925, 108486659931511379162107281251899)

        sage: PR = PolynomialRing(ZZ, 'x,y')
        sage: x, y = PR.gens()
        sage: f = (x+p0)*(y+q0) - N
        sage: f(x0, y0)
        0

        sage: coron_bivariate(f, X=2**112, Y=2**112, k=3)
        ((3330293348008139537089436726746925, 108486659931511379162107281251899),)

    REFERENCES:

    Coron JS. (2004) *Finding Small Roots of Bivariate Integer Polynomial
    Equations Revisited.* In: Cachin C., Camenisch J.L. (eds) Advances in
    Cryptology - EUROCRYPT 2004. EUROCRYPT 2004. Lecture Notes in Computer
    Science, vol 3027. Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/978-3-540-24676-3_29
    """
    from itertools import product, chain

    if pol.nvariables() != 2:
        raise ArithmeticError("Polynomial must be bivariate.")

    PR, (x, y) = pol.parent().objgens()

    delta = max(pol.degrees())
    verbose(f"delta = {delta}", level=1, caller_name='param')

    if pol(0, 0) == 0:
        for xoffset in srange(1, delta+1):
            if pol(xoffset, 0) != 0:
                pol = pol(x+xoffset, y)
                verbose(f"p(0, 0) = 0, use p(x+{xoffset}, y) instead.", level=2, caller_name='param update')
                break
        else:
            raise ValueError("p(0, 0) shouldn't be zero.")
    else:
        xoffset = 0

    p00 = pol(0, 0)

    if gcd(p00, X*Y) != 1:
        verbose("gcd(p(0, 0), XY) is not equals to one, use next primes", level=2, caller_name='param update')

        while gcd(p00, X) != 1:
            X = next_prime(X, proof=False)
        verbose(f"X = 0x{X:x}", level=1, caller_name='param')

        while gcd(p00, Y) != 1:
            Y = next_prime(Y, proof=False)
        verbose(f"Y = 0x{Y:x}", level=1, caller_name='param')

    W = max(abs(coeff) for coeff in pol(x*X, y*Y).coefficients())
    verbose(f"W = 0x{W:x}", level=1, caller_name='param')

    u = W + ((1-W) % abs(p00))
    verbose(f"u = 0x{u:x}", level=1, caller_name='param')

    if X*Y >= W**(2/(3*delta)):
        raise ValueError("Theoretically unsolvable.")

    if k is None:
        warnings.warn("k may be too large, set manually instead.", DeprecationWarning)
        epsilon = 2/(3*delta) - log(X*Y, W)
        k = floor(1 / epsilon)
        verbose(f"k = {k}", level=1, caller_name='param')

    n = u * (X*Y)**k

    q = (inverse_mod(p00, n) * pol.change_ring(Zmod(n))).change_ring(ZZ)

    polys = []
    for i, j in product(srange(k+1), repeat=2):
        verbose(f"X^{k-i} Y^{k-j} x^{i} y^{j} q", level=2, caller_name='add poly')
        polys.append(PR(x**i * y**j * X**(k-i) * Y**(k-j) * q))
    for i, j in product(srange(delta+k+1), repeat=2):
        if i > k or j > k:
            verbose(f"x^{i} y^{j} n", level=2, caller_name='add poly')
            polys.append(x**i * y**j * n)

    monos = []
    for i, j in product(srange(k+1), repeat=2):
        verbose(f"x^{i} y^{j}", level=2, caller_name='add mono')
        monos.append(PR(x**i * y**j))
    for i, j in product(srange(delta+k+1), repeat=2):
        if i > k or j > k:
            verbose(f"x^{i} y^{j}", level=2, caller_name='add mono')
            monos.append(PR(x**i * y**j))

    M = Matrix(ZZ, (delta+k+1)**2)
    for i in srange(M.nrows()):
        for j in srange(M.ncols()):
            M[i, j] = polys[i](X*x, Y*y).monomial_coefficient(monos[j])

    divisor = gcd(list(chain.from_iterable(M)))
    M = (M / divisor).change_ring(ZZ)

    verbose('Matrix M', level=3, caller_name='matrix_overview')
    matrix_overview(M, level=3)

    B = M.LLL(**kwds)

    verbose('Matrix B', level=3, caller_name='matrix_overview')
    matrix_overview(B, level=3)

    v = vector([(mono*divisor)(x/X, y/Y) for mono in monos])
    hs = [PR(row*v) for row in B]

    roots = set()
    for i, h in enumerate(hs):
        # roughly checking
        if DEBUG and sum(abs(ri)*vi(X,Y) for ri,vi in zip(B[i], v)) >= n:
            continue

        Q = pol.resultant(h, y)

        if Q.is_constant():
            continue

        poly_x = Q.univariate_polynomial()
        for x0, _ in poly_x.roots():
            poly_y = pol(x0, y).univariate_polynomial()

            if poly_y.is_constant():
                raise ValueError(f"Polynomial must be irreducible, but the input have factor (x - {x0-xoffset})")

            for y0, _ in poly_y.roots():
                verbose(f"({x0-xoffset}, {y0})", level=2, caller_name='find root')
                roots.add((x0-xoffset, y0))

        if not check_all and roots:
            break

    if DEBUG:
        __import__('IPython').embed()

    return tuple(roots)
