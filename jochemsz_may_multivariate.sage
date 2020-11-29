# -*- coding: utf-8 -*-

load('util.sage')


def _gen_M_(f, m, t):
    PR = f.parent()
    x0 = PR.gen(0)
    M_sub = [set() for _ in range(m+2)]
    f_sup = [set((f**k).monomials()) for k in srange(m+1)]
    l = f.lt() # leading term

    for k in srange(m+1):
        for monomial in f_sup[m]:
            try:
                mono = PR(monomial/(l**k))
            except TypeError:
                continue
            if mono in f_sup[m-k]:
                M_sub[k] |= set(PR(monomial * x0**j) for j in srange(t+1))

    return M_sub


def jochemsz_may_multivariate_mod(pol, *, X_, m, t=0, **kwds):
    """
    Implementation of E. Jochemsz and A. May's Finding Roots of Multivariate Modular Polynomial Equactions

    INPUT:

    - ``pol`` -- a multivariate modular polynomial with small roots
    - ``X_`` -- list of absolute bound for the roots
    - ``m`` -- an integer parameter
    - ``t`` -- an integer parameter for extented strategy (default: 0)
    - ``**kwds`` -- passed through to method :meth:`Matrix_integer_dense.LLL() <sage.matrix.matrix_integer_dense.Matrix_integer_dense.LLL>`.

    EXAMPLES:

    Unfortunately, the output of the LLL algorithm is unlikely to be algebraically independent::

        sage: p = getPrime(64)
        sage: q = getPrime(64)
        sage: N = p * q
        sage: x0 = getRandomNBitInteger(5)
        sage: y0 = getRandomNBitInteger(10)
        sage: sols = (x0, y0)
        sage: sols
        (24, 840)

        sage: PR.<x, y> = PolynomialRing(Zmod(N), order='lex')
        sage: f = 1 + x*y^2 + x^2*y
        sage: f -= f(*sols)
        sage: f(*sols)
        0

        sage: DEBUG = True
        sage: set_verbose(2)
        sage: jochemsz_may_multivariate_mod(f, X_=[2**5, 2**10], m=2)
        verbose 2 (add monos) [1, x*y^2, x^2*y^4]
        verbose 2 (add poly) 1 f^0 N^2
        verbose 2 (add poly) x*y^2 f^0 N^2
        verbose 2 (add poly) x^2*y^4 f^0 N^2
        verbose 2 (add monos) [x^2*y, x^3*y^3]
        verbose 2 (add poly) 1 f^1 N^1
        verbose 2 (add poly) x*y^2 f^1 N^1
        verbose 2 (add monos) [x^4*y^2]
        verbose 2 (add poly) 1 f^2 N^0
        verbose 1 (param) dim = (6, 6)
        verbose 1 (jochemsz_may_multivariate_mod) LLL of 6x6 matrix (algorithm fpLLL:wrapper)
        verbose 1 (jochemsz_may_multivariate_mod) LLL finished (time = 0.015625)
        0 True True
        1 True True
        2 True True
        3 True False
        4 True False
        5 True False
        ...
        ValueError: hs must be algebraically independent

    RSA small d::

        sage: p = getPrime(64)
        sage: q = getPrime(64)
        sage: N = p * q
        sage: phi = (p-1) * (q-1)
        sage: d = getPrime(10)
        sage: e = inverse_mod(d, phi)
        sage: s = p + q - 1
        sage: k = ZZ((e*d-1) // (N-s))

        sage: PR.<x, y> = PolynomialRing(Zmod(e))
        sage: f = N*x + x*y + 1

        sage: x0 = k
        sage: y0 = (-s) % e
        sage: sols = (x0, y0)
        sage: f(*sols)
        0

    REFERENCES:

    Jochemsz E., May A. (2006) *A Strategy for Finding Roots of Multivariate
    Polynomials with New Applications in Attacking RSA Variants.* In: Lai X.,
    Chen K. (eds) Advances in Cryptology – ASIACRYPT 2006. ASIACRYPT 2006.
    Lecture Notes in Computer Science, vol 4284. Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/11935230_18
    """
    if not DEBUG:
        raise NotImplementedError("unfinished")

    PR = pol.parent()
    n = pol.nvariables()

    if PR.term_order() != TermOrder('lex'):
        PR = PolynomialRing(PR.base_ring(), 'x', n, order='lex')
        pol = pol(*PR.gens())
        verbose("use lexicographical order", level=2, caller_name='param update')

    if len(X_) != n:
        raise ValueError("param `X_` must have length of `pol.nvariables()`")

    N = PR.characteristic()
    if N == 0:
        raise ArithmeticError("Input polynomial is defined over `ZZ`. For finding"
            " roots over integers, use `jochemsz_may_multivariate` instead.")

    PR2 = PR.change_ring(ZZ)
    x_ = PR2.gens()

    l = PR2(pol.lt()) # leading term
    al = pol.lc() # leading coefficient

    ff = PR2(al**-1 * pol)

    M_sub = _gen_M_(PR2(pol), m, t)

    det = 1
    monos = []
    polys = []
    for k in srange(m+1):
        new_monos = sorted(M_sub[k].difference(M_sub[k+1]))
        monos += new_monos
        verbose(str(new_monos), level=2, caller_name='add monos')
        for mono in new_monos:
            g = PR2(mono/(l**k) * ff**k * N**(m-k))
            verbose(f"{mono/(l**k)} f^{k} N^{m-k}", level=2, caller_name='add poly')
            det *= mono(*X_) * N**(m-k)
            polys.append(g)

    nrows = len(polys)
    ncols = len(monos)
    verbose(f"dim = ({nrows}, {ncols})", level=1, caller_name='param')

    #if det >= N**(m*(len(monos)+1-n)):
    if det.nbits() >= N.nbits()*(m*(len(monos)+1-n)):
        print((det.nbits() / (N.nbits()*(m*(len(monos)+1-n)))).n())
        #raise ValueError("Theoretically unsolvable.")

    M = Matrix(ZZ, nrows, ncols)
    for i in srange(M.nrows()):
        for j in srange(M.ncols()):
            M[i, j] = polys[i](*(x*X for x, X in zip(x_, X_))).monomial_coefficient(monos[j])

    # det0 = M.det()
    # assert det0 == det

    verbose('Matrix M', level=3, caller_name='matrix overview')
    matrix_overview(M, level=3)

    B = M.LLL(**kwds)

    verbose('Matrix B', level=3, caller_name='matrix overview')
    matrix_overview(B, level=3)

    v = vector([(mono)(*(x/X for x, X in zip(x_, X_))) for mono in monos])
    hs = [PR2(row*v) for row in B]

    if DEBUG:
        for i, h in enumerate(hs):
            print(i, h(*sols) % N**m == 0, h(*sols) == 0)

        if hs[0](*sols) == 0:
            __import__('IPython').embed()

    roots = set()
    for root in solve_hs_resultant(hs[:n]):
        if pol(*root) == 0:
            roots.add(root)

    return tuple(roots)


def jochemsz_may_multivariate(pol, *, X_, m, t=0, **kwds):
    """
    Implementation of E. Jochemsz and A. May's Finding Roots of Multivariate Polynomial Equactions

    INPUT:

    - ``pol`` -- a multivariate polynomial with small roots over integers
    - ``X_`` -- list of absolute bound for the roots
    - ``m`` -- an integer parameter
    - ``t`` -- an integer parameter for extented strategy (default: 0)
    - ``**kwds`` -- passed through to method :meth:`Matrix_integer_dense.LLL() <sage.matrix.matrix_integer_dense.Matrix_integer_dense.LLL>`.

    EXAMPLES::

        sage: p = getPrime(256)
        sage: q = getPrime(256)
        sage: N = p * q
        sage: x0 = p % 2**112
        sage: y0 = q % 2**112
        sage: p0 = p - x0
        sage: q0 = q - y0
        sage: sols = (x0, y0)
        sage: sols
        (4973892006581829278614366425786813, 1552564474804578271979451403535905)

        sage: PR = PolynomialRing(ZZ, 'x,y')
        sage: x, y = PR.gens()
        sage: f = (x+p0)*(y+q0) - N
        sage: f(*sols)
        0

        sage: set_verbose(3)
        sage: jochemsz_may_multivariate(f, X_=[2**112, 2**112], m=4)
        verbose 2 (param update) use lexicographical order
        verbose 1 (param) W = 0x1166101bb...d746b3e03a45cf5e
        verbose 1 (param) R = 0x1166101b...0000000000000
        verbose 2 (add monos) [1, x1, x1^2, x1^3, x0, x0*x1, x0*x1^2, x0*x1^3, x0^2, x0^2*x1, x0^2*x1^2, x0^2*x1^3, x0^3, x0^3*x1, x0^3*x1^2, x0^3*x1^3]
        verbose 2 (add monos) [x1^4, x0*x1^4, x0^2*x1^4, x0^3*x1^4, x0^4, x0^4*x1, x0^4*x1^2, x0^4*x1^3, x0^4*x1^4]
        verbose 1 (param) dim = (25, 25)
        verbose 3 (matrix overview) Matrix M

        000 X X     X X                                       
        001   X X     X X                                     
        002     X X     X X                                   
        003       X       X                 X X               
        004         X X     X X                               
        005           X X     X X                             
        006             X X     X X                           
        007               X       X           X X             
        008                 X X     X X                       
        009                   X X     X X                     
        010                     X X     X X                   
        011                       X       X     X X           
        012                         X X             X X       
        013                           X X             X X     
        014                             X X             X X   
        015                               X       X       X X 
        016                                 X                 
        017                                   X               
        018                                     X             
        019                                       X           
        020                                         X         
        021                                           X       
        022                                             X     
        023                                               X   
        024                                                 X 

        verbose 1 (jochemsz_may_multivariate) LLL of 25x25 matrix (algorithm fpLLL:wrapper)
        verbose 1 (jochemsz_may_multivariate) LLL finished (time = 1.265625)
        verbose 3 (matrix overview) Matrix B

        000 X X X X X X X X X X X X X X X X X X X X X X X X X 
        001 X X X X X X X X X X X X X X X X X X X X X X X X X 
        002 X X X X X X X X X X X X X X X X X X X X X X X X X 
        003 X X X X X X X X X X X X X X X X X X X X X X X X X 
        004 X X X X X X X X X X X X X X X X X X X X X X X X X 
        005 X X X X X X X X X X X X X X X X X X X X X X X X X 
        006 X X X X X X X X X X X X X X X X X X X X X X X X X 
        007 X X X X X X X X X X X X X X X X X X X X X X X X X 
        008 X X X X X X X X X X X X X X X X X X X X X X X X X 
        009 X X X X X X X X X X X X X X X X X X X X X X X X X 
        010 X X X X X X X X X X X X X X X X X X X X X X X X X 
        011 X X X X X X X X X X X X X X X X X X X X X X X X X 
        012 X X X X X X X X X X X X X X X X X X X X X X X X X 
        013 X X X X X X X X X X X X X X X X X X X X X X X X X 
        014 X X X X X X X X X X X X X X X X X X X X X X X X X 
        015 X X X X X X X X X X X X X X X X X X X X X X X X X 
        016 X X X X X X X X X X X X X X X X X X X X X X X X X 
        017 X X X X X X X X X X X X X X X X X X X X X X X X X 
        018 X X X X X X X X X X X X X X X X X X X X X X X X X 
        019 X X X X X X X X X X X X X X X X X X X X X X X X X 
        020 X X X X X X X X X X X X X X X X X X X X X X X X X 
        021 X X X X X X X X X X X X X X X X X X X X X X X X X 
        022 X X X X X X X X X X X X X X X X X X X X X X X X X 
        023 X X X X X X X X X X X X X X X X X X X X X X X X X 
        024 X X X X X X X X X X X X X X X X X X X X X X X X X 

        known roots: []

        j = 2, i = 0, compute resultant of hs[1] and hs[0] with respect to `x1`
        known roots: [4973892006581829278614366425786813]
        ((4973892006581829278614366425786813, 1552564474804578271979451403535905),)

    REFERENCES:

    Jochemsz E., May A. (2006) *A Strategy for Finding Roots of Multivariate
    Polynomials with New Applications in Attacking RSA Variants.* In: Lai X.,
    Chen K. (eds) Advances in Cryptology – ASIACRYPT 2006. ASIACRYPT 2006.
    Lecture Notes in Computer Science, vol 4284. Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/11935230_18
    """
    from itertools import product

    PR = pol.parent()
    n = pol.nvariables()

    if PR.term_order() != TermOrder('lex'):
        PR = PolynomialRing(PR.base_ring(), 'x', n, order='lex')
        pol = PR(pol(*PR.gens()))
        verbose("use lexicographical order", level=2, caller_name='param update')

    if len(X_) != n:
        raise ValueError("param `X_` must have length of `pol.nvariables()`")

    N = PR.characteristic()
    if N != 0:
        raise ArithmeticError("Input polynomial must be defined over integers.")

    x_ = PR.gens()
    d_ = pol.degrees()

    for offset in product(*(srange(dj+1) for dj in reversed(d_))):
        offset = offset[::-1]
        if pol(*offset) != 0:
            f = pol(*(x+xoffset for x, xoffset in zip(x_, offset)))
            break
    if sum(offset):
        verbose(f"a0 = 0, use f({', '.join('x%d+%d' % (i, e) for i, e in enumerate(offset))}) instead.",
            level=2, caller_name='param update')

    a0 = f.constant_coefficient()
    d_ = f.degrees()

    if gcd(a0, prod(X_)) != 1:
        verbose("`gcd(a0, Xj) != 1` for some integer `j`, use next primes.",
            level=2, caller_name='param check')

        X_ = list(X_)
        for j in range(n):
            if gcd(a0, X_[j]) == 1:
                continue
            while gcd(a0, X_[j]) != 1:
                X_[j] = next_prime(X_[j], proof=False)
            verbose(f"X[{j}] = 0x{X_[j]:x}", level=2, caller_name='param update')

    xX_ = tuple(x*X for x, X in zip(x_, X_))

    W = max(abs(coeff) for coeff in pol(*xX_).coefficients())
    W += (1-W) % abs(a0)
    verbose(f"W = 0x{W:x}", level=1, caller_name='param')

    R = W * prod([Xj**(d_[j]*(m-1)) for j, Xj in enumerate(X_)])
    verbose(f"R = 0x{R:x}", level=1, caller_name='param')

    ff = (inverse_mod(a0, R) * f.change_ring(Zmod(R))).change_ring(ZZ)

    S = set()
    for j in srange(t+1):
        S |= set(x_[0]**j * mono for mono in (f**(m-1)).monomials())
    M = set()
    for mono in S:
        M |= set((mono * f).monomials())

    monos = []
    polys = []

    new_monos = sorted(S)
    monos.extend(new_monos)
    verbose(str(new_monos), level=2, caller_name='add monos')

    l_ = PR(sum(S)).degrees()
    for mono in new_monos:
        i_ = mono.degrees()
        g = PR(mono * ff * prod([Xj**(l_[j] - i_[j]) for j, Xj in enumerate(X_)]))
        polys.append(g)

    new_monos = sorted(M.difference(S))
    monos.extend(new_monos)
    verbose(str(new_monos), level=2, caller_name='add monos')

    for mono in new_monos:
        gg = PR(mono * R)
        polys.append(gg)

    nrows = len(polys)
    ncols = len(monos)
    verbose(f"dim = ({nrows}, {ncols})", level=1, caller_name='param')

    det = 1
    M = Matrix(ZZ, nrows, ncols)
    for i in srange(M.nrows()):
        for j in srange(M.ncols()):
            M[i, j] = polys[i](*xX_).monomial_coefficient(monos[j])
        det *= M[i, i]

    if det >= R**(ncols+2-n):
        print((det.nbits() / (ncols+2-n) / R.nbits()).n())
        if not DEBUG: raise ValueError('small m')

    verbose('Matrix M', level=3, caller_name='matrix overview')
    matrix_overview(M, level=3)

    B = M.LLL(**kwds)

    verbose('Matrix B', level=3, caller_name='matrix overview')
    matrix_overview(B, level=3)

    v = vector([(mono)(*(x/X for x, X in zip(x_, X_))) for mono in monos])
    hs = [PR(row*v) for row in B]

    if DEBUG:
        sols1 = [x0-xoffset for x0, xoffset in zip(sols, offset)]
        for i, h in enumerate(hs):
            print(i, h(*sols1) % R == 0, h(*sols1) == 0)

        #if hs[0](*sols1) == 0:
        __import__('IPython').embed()

    roots = set()
    for rt in solve_hs_resultant([f] + hs[:n-1]):
        if f(*rt) == 0:
            root = tuple(x0-xoffset for x0, xoffset in zip(rt, offset))
            # assert pol(*root) == 0
            roots.add(root)

    return tuple(roots)
