from typing import Tuple

def encode(n: int) -> Tuple[int, int]:
    if n == 0:
        return (0, 0)
    else:
        a, b = encode(n // 2)
        return (2*b + n%2, a)

def decode(t: Tuple[int, int]) -> int:
    a, b = t
    if a == 0 and b == 0:
        return 0
    else:
        n = decode((b, a // 2))
        return 2*n + a%2
