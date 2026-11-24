"""Numerical check of Bala's A000139 parity conjecture:
a(n) = 2*(3n)!/((2n+1)!(n+1)!) is odd  <=>  n is an odd fibbinary number (A022341)."""
import sys
from math import factorial as f

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000

def a(n):
    num, den = 2 * f(3 * n), f(2 * n + 1) * f(n + 1)
    assert num % den == 0
    return num // den

def odd_fibbinary(n):
    return n % 2 == 1 and (n & (n >> 1)) == 0

bad = [n for n in range(N) if (a(n) % 2 == 1) != odd_fibbinary(n)]
print(f"checked n < {N}: mismatches = {bad}")
