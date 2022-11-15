from typing import Generic, TypeVar, final
from dataclasses import dataclass

T = TypeVar("T")

class List(Generic[T]): ...

@final
@dataclass
class Cons(List[T]):
    head: T
    tail: List[T]

@final
class Nil(List[T]): ...


a: List[int] = Cons(3, Cons(2, Nil()))

def print_list(l: List[T]) -> None:
    match l:
        case Cons(head, tail):
            print(head)
            print_list(tail)
        case Nil:
            print("***")

print_list(a)
