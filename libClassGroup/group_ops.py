#!/usr/bin/python
#
# (C) 2018 Dan Boneh, Riad S. Wahby <rsw@cs.stanford.edu>

import itertools
import sys

from libClassGroup.group_mixins import _WnafMixin
import libClassGroup.primes as lprimes
import libClassGroup.util as lutil

# python 2/3 hack
if sys.version_info[0] == 2:
    zip = itertools.izip    # pylint: disable=redefined-builtin,no-member
    range = xrange          # pylint: disable=redefined-builtin,undefined-variable

class ClassGroupOps(_WnafMixin):
    def __init__(self, Gdesc):
        self.D = Gdesc.disc
        assert self.D < 0 and self.D % 4 == 1 and lprimes.is_prime(-self.D)
        self.g = Gdesc.g
        self.h = Gdesc.h
        self.id = Gdesc.id
        self.L = Gdesc.L
        assert self.L ** 4 <= -self.D and (self.L + 1) ** 4 > -self.D
        self.desc = (self.D, self.g, self.h)

    # Algorithm 5.4.2 of Cohen's "A Course in Computational Algebraic Number Theory"
    @staticmethod
    def reduce(f):
        (a, b, c) = f

        while True:
            if -a < b <= a:
                if a > c:
                    b = -b
                    (a, c) = (c, a)
                else:
                    if a == c and b < 0:
                        b = -b
                    return (a, b, c)

            (q, r) = divmod(b, 2*a)
            if r > a:
                r -= 2 * a
                q += 1

            c = c - ((b + r) * q) // 2
            b = r

    @staticmethod
    def is_reduced(f):
        (a, b, c) = f
        return (-a < b <= a < c) or (0 <= b <= a == c)

    # NUCOMP of Daniel Shanks
    # Adapted from
    #   Jacobson, M.J. and van der Poorten, A.J., "Computational Aspects of NUCOMP." Proc. ANTS 2002.
    def mul(self, m1, m2):
        if m1[0] == 1:
            return m2
        if m2[0] == 1:
            return m1

        # unpack, swapping m1 and m2 if w1 < w2
        ((u1, v1, w1), (u2, v2, w2)) = (m2, m1) if m1[2] < m2[2] else (m1, m2)

        # Step 1
        s = (v1 + v2) // 2
        m = v2 - s

        # Step 2
        (c, b, F) = lutil.ext_euclid_lr(u1, u2)
        assert u1 * c + u2 * b == F

        # Steps 2--4
        if s % F == 0:
            G = F
            Bx = m * b
            By = u1 // G
        else:
            (y, G) = lutil.ext_euclid_l(s, F)
            assert (G - y *s) % F == 0
            H = F // G
            By = u1 // G
            # Step 4
            l1 = (b * (w1 % H)) % H
            l2 = (c * (w2 % H)) % H
            l = (y * (l1 + l2)) % H
            Bx = b * m // H + l * By // H
        Cy = u2 // G
        Dy = s // G

        # Step 5 (truncated Euclidean division)
        (bx, by) = (Bx % By, By)
        (x, y, z) = (1, 0, 0)
        while bx != 0 and abs(by) > self.L:
            ((q, bx), by) = (divmod(by, bx), bx)
            (y, x) = (x, y - q * x)
            z += 1
        (by, y) = (-by, -y) if z % 2 == 1 else (by, y)
        (ax, ay) = (G * x, G * y)

        # Steps 6--7
        if z == 0:
            # Step 6
            Q1 = Cy * bx
            (cx, dx) = ((Q1 - m) // By, (bx * Dy - w2) // By)
            ret = (by * Cy, v2 - 2 * Q1, bx * cx - G * dx)
        else:
            # Step 7
            (cx, dx) = ((Cy * bx - m * x) // By, (Dy * bx - w2 * x) // By)
            (Q1, Q3) = (by * cx, y * dx)
            (Q2, Q4) = (Q1 + m, Q3 + Dy)
            dy = Q4 // x
            cy = Q2 // bx if bx != 0 else (cx * dy - w1) // dx
            ret = (by * cy - ay * dy, G * (Q3 + Q4) - Q1 - Q2, bx * cx - ax * dx)

        assert self.discrim(ret) == self.D
        return self.reduce(ret)

    # NUCOMP of Daniel Shanks
    # Adapted from
    #   Jacobson, M.J. and van der Poorten, A.J., "Computational Aspects of NUCOMP." Proc. ANTS 2002.
    def sqr(self, m):
        if m[0] == 1:
            return m
        (u, v, w) = m

        # Step 1
        (y, G) = lutil.ext_euclid_l(v, u)
        (By, Dy) = (u // G, v // G)

        # Step 2
        Bx = (y * w) % By

        # Step 3
        (bx, by) = (Bx, By)
        (x, y, z) = (1, 0, 0)
        while bx != 0 and abs(by) > self.L:
            ((q, bx), by) = (divmod(by, bx), bx)
            (y, x) = (x, y - q * x)
            z += 1
        (by, y) = (-by, -y) if z % 2 == 1 else (by, y)
        (ax, ay) = (G * x, G * y)

        # Steps 4--5
        if z == 0:
            # Step 4
            dx = (bx * Dy - w) // By
            (u3, w3) = (by ** 2, bx ** 2)
            ret = (u3, v - (bx + by) ** 2 + u3 + w3, w3 - G * dx)
        else:
            # Step 5
            dx = (bx * Dy - w * x) // By
            Q1 = dx * y
            dy = Q1 + Dy
            v3 = G * (dy + Q1)
            dy = dy // x
            (u3, w3) = (by ** 2, bx ** 2)
            ret = (u3 - ay * dy, v3 - (bx + by) ** 2 + u3 + w3, w3 - ax * dx)

        assert self.discrim(ret) == self.D
        return self.reduce(ret)

    @staticmethod
    def discrim(m):
        (a, b, c) = m
        return b * b - 4 * a * c

    @staticmethod
    def inv(m):
        (a, b, c) = m
        return (a, -b, c)
