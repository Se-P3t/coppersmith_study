# -*- coding: utf-8 -*-

load('util.sage')


def univariate_modular(pol, *, X, m=None, t=None, beta=1, strict=True, **kwds):
    r"""
    Solving Univariate Modular Equation with Small Root

    INPUT:

    - ``pol`` -- a univariate polynomial with small root
    - ``X`` -- an absolute bound for the root
    - ``m`` -- an integer parameter
    - ``beta`` -- compute a root mod `b` where `b` is a factor of `N` and `b \ge
      N^\beta`. (Default: 1, so `b = N`.)
    - ``strict`` -- (bool) ``True`` for checking the bound of roots
    - ``**kwds`` -- passed through to method :meth:`Matrix_integer_dense.LLL()
      <sage.matrix.matrix_integer_dense.Matrix_integer_dense.LLL>`.

    EXAMPLES:

    We examine the approach by solving the example used in cf.[1] Sec.4::

        sage: N = 35
        sage: F = Zmod(N)
        sage: PR = PolynomialRing(F, 'x')
        sage: x = PR.gen()
        sage: pol = x^2 + 14*x + 19

        sage: univariate_modular(pol, X=4, h=3)
        [3]

    Note that this method will still find the solution even though `x_0 > X`::

        sage: univariate_modular(pol, X=2, h=3, strict=False)
        [3]

    Next, we apply a stereotyped message attack::

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

    The built-in function ``small_roots`` of sagemath accepts the parameter
    `epsilon`, but a decimal is difficult to choose::

        sage: pol.small_roots(X=1<<nbits)
        []
        sage: pol.small_roots(X=1<<nbits, epsilon=0.05)
        [36558277155...4686973659]

    It is easier to use an integer as a parameter (You can simply keep adding
    one to it until you find the solution)::

        sage: set_verbose(1)
        sage: univariate_modular(pol, X=1<<nbits)
        verbose 1 (param) epsilon = 0.142857142857143
        verbose 1 (param) m = 3
        verbose 1 (param) t = 0
        verbose 1 (univariate_modular) LLL of 9x12 matrix (algorithm fpLLL:wrapper)
        verbose 1 (univariate_modular) LLL finished (time = 0.03125)
        []
        sage: univariate_modular(pol, X=1<<nbits, m=6)
        [36558277155...4686973659]

    Additionally, we can factor RSA modulus with leaking information::

        sage: nbits = 400
        sage: x0 = p % (1<<nbits)
        sage: p_bar = p - x0

        sage: pol = x + p_bar
        sage: x0
        254963813...95167949637
        sage: gcd(ZZ(pol(x0)), N) == p
        True

    For a balanced modulus `N = pq`, the unknown divisor should be bigger than
    `N^0.49`, thus we can set the parmeter `beta` equal to 0.49::

        sage: set_verbose(3)
        sage: univariate_modular(pol, X=1<<nbits, beta=0.49)
        verbose 1 (param) epsilon = 0.0700000000000000
        verbose 1 (param) m = 4
        verbose 1 (param) t = 4
        verbose 3 (matrix_overview) Matrix M

        000 X               
        001 X X             
        002 X X X           
        003 X X X X         
        004 X X X X X       
        005   X X X X X     
        006     X X X X X   
        007       X X X X X 

        verbose 1 (univariate_modular) LLL of 8x8 matrix (algorithm fpLLL:wrapper)
        verbose 1 (univariate_modular) LLL finished (time = 0.015625)
        verbose 3 (matrix_overview) Matrix B

        000 X X X X X X X X 
        001 X X X X X X X X 
        002 X X X X X X X X 
        003 X X X X X X X X 
        004 X X X X X X X X 
        005 X X X X X X X X 
        006 X X X X X X X X 
        007 X X X X X X X X 

        verbose 2 (potential roots) [254963...167949637]
        verbose 2 (find roots) [254963813...495167949637]
        [2549638136...4495167949637]

    REFERENCES:

    N. Howgrave-Graham. *Finding small roots of univariate modular equations
    revisited.* In M. Darnell, editor, IMA Int. Conf., volume 1355 of
    Lecture Notes in Computer Science, pages 131–142. Springer, 1997.
    https://doi.org/10.1007/BFb0024458

    A. May. *Using LLL-reduction for solving RSA and factorization problems:
    A survey.* LLL+25 Conference in honour of the 25th birthday of the LLL
    algorithm, 2007.
    https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.86.9408&rep=rep1&type=pdf

    Alexander May. *New RSA Vulnerabilities Using Lattice Reduction Methods.*
    PhD thesis, University of Paderborn, 2003.
    https://www.math.uni-frankfurt.de/~dmst/teaching/WS2015/Vorlesung/Alex.May.pdf
    """
    PR = pol.parent()

    N = PR.characteristic()
    if N == 0:
        raise ValueError("Input polynomial must be defined over Z/nZ.")

    if not pol.is_monic():
        pol = pol.monic()
        verbose("Polynomial must be monic.", level=2, caller_name='param update')

    beta = RR(beta)
    if beta <= 0.0 or beta > 1.0:
        raise ValueError("0.0 < beta <= 1.0 not satisfied.")

    f = pol.change_ring(ZZ)

    PR, (x,) = f.parent().objgens()

    delta = f.degree()

    if m is None:
        epsilon = beta / 7
        verbose(f"epsilon = {epsilon}", level=1, caller_name='param')

        m = ceil(max(beta**2/(delta*epsilon), 7*beta/delta))
        verbose(f"m = {m}", level=1, caller_name='param')
    
    if t is None:
        t = floor(delta*m*(1/beta - 1))
        verbose(f"t = {t}", level=1, caller_name='param')

    g = [x**j * N**(m-i) * f**i for i in srange(m) for j in srange(delta)]
    g.extend([x**i * f**m for i in srange(t)])

    M = Matrix(ZZ, len(g), delta*m+max(delta,t))
    for i in srange(M.nrows()):
        for j in srange(M.ncols()):
            M[i, j] = g[i](x*X).monomial_coefficient(x**j)

    verbose('Matrix M', level=3, caller_name='matrix overview')
    matrix_overview(M, level=3)

    B = M.LLL(**kwds)

    verbose('Matrix B', level=3, caller_name='matrix overview')
    matrix_overview(B, level=3)

    if DEBUG:
        for j in range(M.nrows()):
            poly_sol = PR([(e / X**i) for i, e in enumerate(B[j])])
            print(gcd(N, poly_sol(x0)) >= N**beta)

    poly_sol = PR([(e / X**i) for i, e in enumerate(B[0])])

    potential_roots = [ZZ(rt[0]) for rt in poly_sol.roots()]
    verbose(str(potential_roots), level=2, caller_name='potential roots')

    roots = []
    for root in potential_roots:
        if strict and abs(root) >= X:
            continue
        result = f(root)
        if gcd(N, result) >= N**beta:
            roots.append(root)
    
    verbose(str(roots), level=2, caller_name='find roots')

    if DEBUG:
        __import__('IPython').embed()

    return roots
