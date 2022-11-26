from typing import Generic, TypeVar, final, Union
from dataclasses import dataclass

T = TypeVar("T")

LinkedList = Union['Cons[T]', 'Nil[T]']

@final
@dataclass
class Cons(Generic[T]):
    head: T
    tail: 'LinkedList[T]'

@final
@dataclass
class Nil(Generic[T]): ...
