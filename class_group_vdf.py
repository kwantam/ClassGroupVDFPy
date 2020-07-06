#/usr/bin/python3
#
# VDF based on class group / Wesolowski proof
#
# (C) 2020 Riad S. Wahby <rsw@cs.stanford.edu>

from random import getrandbits

from libClassGroup.group_desc import cg_desc
from libClassGroup.group_ops import ClassGroupOps
from libClassGroup.primes import next_prime

# -d is a 1536-bit prime such that d % 8 == 1
d = -1485005631604802232190696484259162228974543902507530074468559549683187163147773354143439965850463058663711567897833577130409904508966573167558129033274643057505844784332692342042319966129273607097759974247629782760738124676876428867307893395028250988373038509108745370004813510632437079986165060801411816546149682161168286652249859440785033844265772771612275074918711347938476828020438951995140527379914811065211074084258988924780500454887242908812696089490302751
cg = ClassGroupOps(cg_desc(d))

# T is the work factor. Let's start with something small...
T = 1024

def vdf_and_proof():
    # pick a random input x (normally this would be chosen by hashing some agreed-upon value)
    x = cg.pow(cg.g, getrandbits(64))
    
    # step 1 (prover): compute x^(2^T)
    y = x
    for _ in range(0, T):
        y = cg.sqr(y)
    y = cg.reduce(y)
    
    # step 2 (verifier): choose random challenge prime
    # in a non-interactive VDF, this would be chosen by hashing (d, g, T, x, y)
    # note that next_prime does not give a uniform prime, but this is probably OK for us
    l = next_prime(getrandbits(264))
    
    # step 3 (prover): compute x^((2^T) // l), where // is floor division
    # in principle, we're doing something like this:
    ## (q, r) = divmod(1 << T, l)
    ## pi = cg.pow(x, q)
    # but we can do it without materializing q and r via long division
    # see Section 2.1 of Boneh, Buenz, Fisch, "A survey of two verifiable delay functions." ePrint 2018/712.
    pi = cg.id
    rem = 1
    for _ in range(0, T):
        pi = cg.sqr(pi)
        if (2 * rem) // l == 1:
            pi = cg.mul(pi, x)
        rem = (2 * rem) % l
    pi = cg.reduce(pi)
    
    # step 4 (verifier): check that pi^l * x^r == y, where r == 2^T mod l
    # pow2(g1, e1, g2, e2) computes g1^e1 * g2^e2
    r = (1 << T) % l
    lhs = cg.pow2(pi, l, x, r)
    lhs = cg.reduce(lhs)
    assert lhs == y

if __name__ == "__main__":
    for _ in range(0, 4):
        vdf_and_proof()
