#!/usr/bin/python
#
# (C) 2018 Dan Boneh, Riad S. Wahby <rsw@cs.stanford.edu>

from itertools import chain
import math
import random
import sys

# python 2/3 hack
if sys.version_info[0] == 2:
    range = xrange      # pylint: disable=redefined-builtin,undefined-variable

rand = random.SystemRandom()

# ceiling of log2
def clog2(val):
    if isinstance(val, float):
        val = int(math.ceil(val))
    return (val-1).bit_length()

def invert_modp(val, prime):
    if val % prime == 0:
        return None
    (inv, d) = ext_euclid_l(val % prime, prime)
    if d != 1:
        return None
    assert (inv * val - 1) % prime == 0
    return inv % prime

def gcd(a, b):
    if sys.version_info[0] == 3:
        return math.gcd(a, b)   # pylint: disable=no-member
    while b != 0:
        (a, b) = (b, a % b)
    return a

def ext_euclid_l(a, b):
    (t, t_, r, r_) = (1, 0, a, b)

    while r != 0:
        ((quot, r), r_) = (divmod(r_, r), r)
        (t_, t) = (t, t_ - quot * t)

    return (t_, r_)

_q_storage = [None] * 65536
def ext_euclid_lr(a, b):
    (r, r_) = (a, b)
    idx = 0

    # compute GCD, store quotients
    while r_ != 0:
        ((_q_storage[idx], r_), r) = (divmod(r, r_), r_)
        idx += 1

    # use quotients to reconstruct Bezout coefficients
    (s, t, imod) = (1, -1, idx % 2)
    for jdx in reversed(range(imod, idx, 2)):
        s = s - t * _q_storage[jdx+1]
        t = t - s * _q_storage[jdx]
    if imod == 1:
        s = s - t * _q_storage[0]
        (s, t) = (t, s)

    if r < 0:
        # make sure gcd is positive
        (r, s, t) = (-r, -s, -t)
    if abs(a) != r and abs(b) != r:
        # reduce Bezout coefficients
        tmod = abs(a // r)
        smod = abs(b // r)
        t = t % tmod - (tmod if t < 0 else 0)
        s = s % smod - (smod if s < 0 else 0)
    assert a*s + b*t == r, "%d * %d + %d * %d != %d" % (a, s, b, t, r)
    return (s, t, r)

def num_to_bits(n, pad=None):
    bit_iter = ( b == "1" for b in bin(int(n))[2:] )
    if pad is None:
        return bit_iter
    return chain(( False for _ in range(0, pad - n.bit_length()) ), bit_iter)

# compute Jacobi symbol, n prime or composite
def jacobi(a, n):
    if n <= 0 or n % 2 == 0:
        raise ValueError("Jacobi symbol (a/n) is undefined for negative, zero, and even n")

    negate = False
    a = a % n
    while a != 0:
        while a % 2 == 0:
            a = a // 2
            if n % 8 == 3 or n % 8 == 5:
                negate = not negate

        if a % 4 == 3 and n % 4 == 3:
            negate = not negate

        (n, a) = (a, n)

        a = a % n

    if n == 1:
        return -1 if negate else 1

    return 0

# essentially https://en.wikipedia.org/wiki/Integer_square_root
def isqrt(n):
    if n < 0:
        raise ValueError("isqrt called with negative input")

    shift = max(0, 2 * ((int(n).bit_length() + 1) // 2) - 2)
    res = 0
    while shift >= 0:
        res <<= 1
        res_c = res + 1
        if (res_c * res_c) <= (n >> shift):
            res = res_c
        shift -= 2

    return res

def factor_twos(n):
    d = n
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    return (d, s)

# Tonelli-Shanks
def sqrt_modp(n, p):
    n = n % p
    if n == 0:
        return 0

    if jacobi(n, p) == -1:
        return None

    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)

    # factor out 2^s from p - 1
    (Q, s) = factor_twos(p - 1)

    # find a non-residue mod p
    w = 2
    while jacobi(w, p) != -1:
        w += 1

    w = pow(w, Q, p)
    y = pow(n, Q, p)
    q = pow(n, (Q + 1) // 2, p)

    while True:
        y_save = y
        i = 0
        while i < s and y != 1:
            y = pow(y, 2, p)
            i += 1
        if i == 0:
            break
        if i == s:
            return None

        w = pow(w, 1 << (s - i - 1), p)
        s = i
        q = (q * w) % p
        w = pow(w, 2, p)
        y = (y_save * w) % p

    if q > (p // 2):
        q = p - q

    assert n == (q * q) % p
    return q

# sqrt mod a product of primes
def sqrt_modn(x, p, q):
    sqrtP = sqrt_modp(x, p)
    sqrtQ = sqrt_modp(x, q)

    if sqrtP is None or sqrtQ is None:
        return None

    (mP, mQ, _) = ext_euclid_lr(p, q)

    return (sqrtQ * mP * p + sqrtP * mQ * q) % (p * q)

# from https://stackoverflow.com/questions/1167617/in-python-how-do-i-indicate-im-overriding-a-method
def overrides(interface_class):
    def overrider(method):
        assert method.__name__ in dir(interface_class)
        return method
    return overrider
