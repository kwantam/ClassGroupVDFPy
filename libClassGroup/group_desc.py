#!/usr/bin/python
#
# (C) 2020 Riad S. Wahby <rsw@cs.stanford.edu>

from collections import namedtuple
import sys

import libClassGroup.util as lutil

# python 2/3 hack
if sys.version_info[0] == 2:
    range = xrange          # pylint: disable=redefined-builtin,undefined-variable

ClassGroupDesc = namedtuple("ClassGroupDesc", "disc g id L")

# find a member of the class group of discriminant disc with a=a
def _gen_CG_elm(a, disc):
    a4 = 4 * a
    for b in range(0, a + 1):
        bsqD = b * b - disc
        if bsqD % a4 == 0:
            return (a, b, bsqD // a4)
    return None

def cg_desc(disc):
    if disc >= 0 or disc % 4 != 1:
        return None
    one = _gen_CG_elm(1, disc)
    g = None
    for ga in range(2, 65536):
        g = _gen_CG_elm(ga, disc)
        if g is not None:
            break
    if g is None:
        return None
    L = lutil.isqrt(lutil.isqrt(-disc))
    while (L + 1) ** 4 < -disc:
        L += 1
    return ClassGroupDesc(disc, g, one, L)
