#!/usr/bin/python
#
# (C) 2018 Dan Boneh, Riad S. Wahby <rsw@cs.stanford.edu>

import itertools
import sys

# python 2/3 hack
if sys.version_info[0] == 2:
    zip = itertools.izip    # pylint: disable=redefined-builtin,no-member
    range = xrange          # pylint: disable=redefined-builtin,undefined-variable

class _WnafMixin(object):
    WINSIZE = 6

    def _precomp_wnaf(self, b, winsize):
        tablen = 1 << (winsize - 2)
        pctab = [None] * tablen
        bSq = self.sqr(b)
        pctab[0] = b
        for i in range(1, tablen):
            pctab[i] = self.mul(pctab[i-1], bSq)
        return pctab

    def _one_mul(self, ret, w, pctabP):
        if w > 0:
            ret = self.mul(ret, pctabP[(w-1)//2])
        elif w < 0:
            ret = self.mul(ret, self.inv(pctabP[(-1-w)//2]))
        return ret

    @staticmethod
    def _wnaf(r, w, bitlen=None):
        if bitlen is None:
            bitlen = r.bit_length() + 1
        out = [None] * bitlen
        for i in reversed(range(0, bitlen)):
            val = 0
            if r % 2:
                val = r & ((1<<w)-1)
                if val & (1<<(w-1)):
                    val -= (1<<w)
                r -= val
            out[i] = val
            r = r >> 1
        assert r == 0
        return out

    def pow(self, b, e):
        pctabP = self._precomp_wnaf(b, self.WINSIZE)
        ebits = self._wnaf(e, self.WINSIZE)

        ret = self.id
        for w in ebits:
            if ret != self.id:
                ret = self.sqr(ret)
            ret = self._one_mul(ret, w, pctabP)

        return ret

    def pow2(self, b1, e1, b2, e2):
        pctabP1 = self._precomp_wnaf(b1, self.WINSIZE)
        pctabP2 = self._precomp_wnaf(b2, self.WINSIZE)

        totlen = max(e1.bit_length(), e2.bit_length()) + 1
        e1bits = self._wnaf(e1, self.WINSIZE, totlen)
        e2bits = self._wnaf(e2, self.WINSIZE, totlen)

        ret = self.id
        for (w1, w2) in zip(e1bits, e2bits):
            if ret != self.id:
                ret = self.sqr(ret)
            ret = self._one_mul(ret, w1, pctabP1)
            ret = self._one_mul(ret, w2, pctabP2)

        return ret
