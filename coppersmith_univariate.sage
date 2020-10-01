# -*- coding: utf-8 -*-

load('util.sage')


def coppersmith_univariate(pol, *, X, h=None, strict=False, review=False, **kwds):
    r"""
    Implementaion of Coppersmith's Solving Univariate Modular Equation with Small Root.

    INPUT:

    - ``pol`` -- a monic univariate polynomial with small root
    - ``X`` -- an absolute bound for the root
    - ``h`` -- an integer parameter
    - ``strict`` -- (bool) ``True`` for checking the parameter `X`
    - ``review`` -- (bool) ``True`` for using Howgrave-Graham's review
    - ``**kwds`` -- passed through to method :meth:`Matrix_integer_dense.LLL() <sage.matrix.matrix_integer_dense.Matrix_integer_dense.LLL>`.

    EXAMPLES::

        sage: N = 35
        sage: F = Zmod(N)
        sage: PR = PolynomialRing(F, 'x')
        sage: x = PR.gen()
        sage: pol = x^2 + 14*x + 19

        sage: coppersmith_univariate(pol, X=2, h=3)
        [3]

    REFERENCES:

    Don Coppersmith. *Finding a small root of a univariate modular equation.*
    In Advances in Cryptology, EuroCrypt 1996, volume 1070 of Lecture
    Notes in Computer Science, p. 155--165. Springer, 1996.
    http://cr.yp.to/bib/2001/coppersmith.pdf

    N. Howgrave-Graham. *Finding small roots of univariate modular equations
    revisited.* In M. Darnell, editor, IMA Int. Conf., volume 1355 of
    Lecture Notes in Computer Science, pages 131–142. Springer, 1997.
    https://doi.org/10.1007/BFb0024458
    """
    # warnings.warn("This function is not effictive, "
    #     "use `sage_small_roots` or `howgrave_univariate` instead.", DeprecationWarning)

    if not pol.is_monic():
        raise ArithmeticError("Polynomial must be monic.")

    N = pol.parent().characteristic()

    f = pol.change_ring(QQ)

    P, (x,) = f.parent().objgens()

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

    if review:
        Xmax = ((4/3)**(-1/2) * (h*k)**(-1/(h*k-1))) * N**((h-1)/(h*k-1))
    else:
        Xmax = 1/2 * N**(1/k-epsilon)
    if strict and X >= Xmax:
        raise ValueError("Theoretically unsolvable.")

    qij = {}
    for i in srange(k):
        for j in srange(1, h):
            qij[i, j] = x**i * f**j

    A = Matrix(QQ, h*k, h*k - k)
    for g in srange(h*k):
        for i in srange(k):
            for j in srange(1, h):
                # `\gamma(i, j)` is defined by `hk+i+(j-1)k`,
                # in this sub-matrix, we need to subtract the offset `hk`
                A[g, i+(j-1)*k] = qij[i, j].monomial_coefficient(x**g)

    D_prime = Matrix(QQ, h*k - k)
    for i in srange(h*k - k):
        D_prime[i, i] = N**(i//k + 1)

    D = Matrix(QQ, h*k)
    if review:
        delta = 1
    else:
        delta = QQ((1 / sqrt(h*k)).n(100))
    for g in srange(h*k):
        D[g, g] = delta * X**-g

    O = Matrix(QQ, h*k-k, h*k)

    M = block_matrix([
        [D, A],
        [O, D_prime]
    ])

    verbose('Matrix M', level=3, caller_name='matrix_overview')
    matrix_overview(M, level=3)

    HM = copy(M)

    for i in srange(h*k):
        for g in srange(2*h*k-k-1, h*k-1, -1):
            HM.swap_rows(i, g)

    HM = block_matrix([
        [HM[h*k-k : h*k]],
        [HM[:h*k-k]],
        [HM[h*k:]]
    ])

    verbose('Matrix HM', level=3, caller_name='matrix_overview')
    matrix_overview(HM, level=3)

    # Do elementary row operations for transform to identity matrix at lower-right.
    for i in srange(h*k, 2*h*k - k):
        for g in srange(h*k, 2*h*k - k):
            pivot = HM[g, i]
            if pivot != 0:
                if g == i:
                    pivot = pivot - 1
                HM.add_multiple_of_row(g, i, -pivot)

    # Do elementary row operations for transform to zero matrix at upper-right.
    for i in srange(h*k, 2*h*k-k):
        for g in srange(h*k):
            pivot = HM[g, i]
            if pivot != 0:
                HM.add_multiple_of_row(g, i, -pivot)

    M_hat = HM[0:h*k, 0:h*k]
    # transform to lower-triangle matrix
    M_hat, _ = M_hat._clear_denom()
    for i in srange(h*k):
        M_hat[i] = M_hat[i][::-1]
    M_hat = M_hat[::-1]

    verbose('Matrix M_hat', level=3, caller_name='matrix_overview')
    matrix_overview(M_hat, level=3)

    B = M_hat.LLL(**kwds)

    verbose('Matrix B', level=3, caller_name='matrix_overview')
    matrix_overview(B, level=3)

    H_1 = M * HM**-1
    H_2 = M_hat * B**-1

    # Constuct Polynomial Vector: (1, x0, ..., x0^{hk-1}, -y0, -y0x0, ..., -y0x0^{k-1}, ..., -y0^{h-1}x0^{k-1})
    v = Matrix(P, 1, 2*h*k-k)
    for i in srange(h*k):
        v[0, i] = x**i

    for i in srange(1, h):
        for j in srange(k):
            v[0, h*k + (i-1)*k + j] = -x**j * (f**i / N**i)

    pol_sol = (v*H_1)[0][:h*k] * (H_2.T)[h*k-1][::-1]

    # Finding roots for `x`
    roots = []
    for x_candidate in map(lambda t: t[0], (pol_sol).roots()):
        if x_candidate.denom() != 1:
            continue
        x_candidate = ZZ(x_candidate)
        if pol(x_candidate) == 0:
            roots += [x_candidate]

    if DEBUG:
        __import__('IPython').embed()

    return roots
