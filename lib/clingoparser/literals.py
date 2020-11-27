from typing import NamedTuple, Union, List
from dataclasses import dataclass
from clingo import Symbol # type: ignore # pylint: disable=import-error, unused-import, no-name-in-module
from sign import Sign


@dataclass(eq=True, unsafe_hash=True, order=True)
class Literal:
    atom: Symbol
    sign: Sign

    def __init__(self, atom: Symbol, sign: Union[Sign, bool]):
        self.atom = atom
        if isinstance(sign, bool):
            if sign:
                sign = Sign.NoSign
            else:
                sign = Sign.Negation
        self.sign = sign

    def __repr__(self):
        return repr(self.sign) + repr(self.atom)


@dataclass(eq=True, unsafe_hash=True, order=True)
class EpistemicLiteral:
    literal: Literal
    sign: Sign = Sign.NoSign

    def __str__(self):
        return f'{self.sign}&k{{ {self.literal} }}'

    # def __init__(self, literal: Literal, sign: Sign):
    #     self.literal  = literal
    #     self.sign = sign

    # def __repr__(self):
    #     return f'{self.sign}&k{{ {self.literal} }}'

    # def __eq__(self, other):
    #     return self.literal == other.literal and self.sign == other.sign

    # def __lt__(self, other):
    #     return (self.literal, self.sign) \
    #         < (other.literal, other.sign)

class WorldView(NamedTuple):
    symbols: List[EpistemicLiteral]

    def __str__(self):
        return ' '.join(map(str, sorted(self.symbols)))
