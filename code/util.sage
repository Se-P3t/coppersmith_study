# -*- coding: utf-8 -*-
"""
basic functions for coppersmith's method
"""
from sage.misc.verbose import verbose

try:
    DEBUG
except NameError:
    DEBUG = 0


def n2b(n, blocksize=0):
    """
    Convert an integer to a byte string
    """
    n = int(n)
    s = n.to_bytes((n.bit_length() + 7) // 8, 'big')

    if blocksize > 0 and len(s) % blocksize:
        s = (blocksize - len(s) % blocksize) * b'\x00' + s
    return s


def b2n(s):
    """
    Convert a byte string to a integer
    """
    return int.from_bytes(s, 'big')


def getRandomNBitInteger(N):
    """
    Return a random N-bit number.
    """
    return randint(1<<(N-1), (1<<N)-1)


def getPrime(N):
    """
    Return a random N-bit prime number.
    """
    return random_prime((1<<N)-1, lbound=1<<(N-1))


def iroot(number, exponent):
    """
    Return the integer root of number and boolean value that is True iff
    the root is exact
    """
    root = number**(1/exponent)
    if root.parent() == RationalField():
        return (ZZ(root), True)
    elif root.parent() == SR:
        return (ZZ(root.round()), False)
    raise TypeError


def matrix_overview(BB, level=2, bound = None):
    """
    Print a matrix overview if the current verbosity is at least level.
    """
    if get_verbose() >= level:
        mid = ''
        if BB.nrows() < 60:
            mid = ' '
        print()
        for ii in range(BB.nrows()):
            a = f'{ii:03d} '
            for jj in range(BB.ncols()):
                B_ij = abs(BB[ii, jj])
                if B_ij == 0:
                    a += ' '
                elif B_ij == 1:
                    a += '1'
                elif B_ij < 1:
                    a += '.'
                else:
                    a += 'X'
                a += mid
            if bound is not None and BB[ii,ii] > bound:
                a += '~'
            print(a)
        print()


def solve_hs_bruteforce(hs, nbits, check=True):
    r"""
    solve multivariate polynomial system with bit-by-bit bruteforcing from LSB to MSB

    origin: https://gist.github.com/hellman/a2c2221f3065eeb0a7dd975921dad43a#file-0_writeup-py-L99-L127
    """
    from itertools import product

    level = get_verbose()

    nvar = hs[0].nvariables()
    sols = {tuple(0 for _ in range(nvar))}
    hsmod = [h.change_ring(Zmod(2**nbits)) for h in hs]

    pre = '\r'
    for i in range(nbits):
        if check and len(sols)*2**nvar > 1024:
            raise ValueError("too much solutions")

        sols2 = set()
        mod = 2**i
        polys = [h.change_ring(Zmod(2*mod)) for h in hsmod]
        for bits in product(range(2), repeat=nvar):
            for sol in sols:
                guess_sol = tuple(sol_i+bit*mod for sol_i, bit in zip(sol, bits))
                if any(poly(*guess_sol) for poly in polys):
                    continue
                sols2.add(guess_sol)

        if not sols:
            raise ValueError("no solution was found")
        if len(sols2) != len(sols):
            if level >= 2:
                pre = '\n'
            else:
                pre = '\r'
        sols = sols2

        if level >= 1:
            print(f"{pre}solving... {i+1}/{nbits} - {len(sols)} solution(s)", end='')
            pre = '\r'

    if check:
        if level >= 1:
            print('\nchecking... (over ZZ)')
        sols = {sol for sol in sols if all(poly(*sol) == 0 for poly in hs)}
        if level >= 1:
            print(f'done - find {len(sols)} solution(s)')
    else:
        if level >= 1:
            print(f'\ndone - find {len(sols)} solution(s) over Zmod(2^{nbits})')

    for sol in sols:
        yield sol


def solve_hs_resultant(hs, root = None):
    """
    solve multivariate polynomial system with resultant

    !!! not tested !!!
    """
    level = get_verbose()
    n = hs[0].nvariables()

    if root is None:
        root = []
        if len(hs) != n:
            raise ValueError("hs must have the length of `pol.nvariables()`")

    if level >= 2:
        print(f"known roots: {root}")

    idx = len(root)
    hs = copy(hs)

    x_ = hs[0].parent().gens()
    hs = [h(*(root + list(x_[idx:]))) for h in hs]

    if idx == n - 1:

        root_x0 = [ZZ(rt[0]) for rt in hs[0].univariate_polynomial().roots()]
        if not root_x0:
            raise ValueError("no solution")

        for x0 in root_x0:
            yield tuple([*root, x0])

    else:

        hs0 = copy(hs)

        if level >= 2:
            pre = '\n'
        else:
            pre = '\r'

        for j in range(n - idx, 1, -1):
            new_hs = []
            hj = hs[j-1]

            for i in range(j-1):

                if level >= 1:
                    print(f"{pre}j = {j}, i = {i}, compute resultant of hs[{j-1}] and hs[{i}] with respect to `{x_[j-1]}`", end='')

                new_hi = hs[i].resultant(hj, x_[j-1])
                if new_hi.is_constant():
                    raise ValueError("hs must be algebraically independent")
                new_hs.append(new_hi)

            hs = new_hs

        if level >= 1:
            print()

        root_x0 = [ZZ(rt[0]) for rt in hs[0].univariate_polynomial().roots()]
        if not root_x0:
            raise ValueError("no solution")

        for x0 in root_x0:
            yield from solve_hs_resultant(hs0[:-1], root + [x0])




