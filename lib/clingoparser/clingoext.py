from typing import NamedTuple, Union, List, Callable, Tuple, Any
import clingo  # type: ignore
from clingo.ast import AST  # type: ignore # pylint: disable=import-error, unused-import, no-name-in-module
from clingo import MessageCode, Symbol, TruthValue  # type: ignore # pylint: disable=import-error, unused-import, no-name-in-module
from groundprogram import GroundProgram, ClingoRule, ClingoOutputAtom, ClingoWeightRule, ClingoProject, ClingoExternal










class Control(object):  # type: ignore

    def __init__(self, arguments: List[str] = [], logger: Callable[[MessageCode, str], None] = None, message_limit: int = 20, control: clingo.Control = None): # pylint: disable=dangerous-default-value
        if control is None:
            control = clingo.Control(list(arguments), logger, message_limit)
        self.control = control
        self.non_ground_program: List[AST] = []
        self.ground_program = GroundProgram()
        self.control.register_observer(Observer(self.ground_program))

    def ground(self, parts: List[Tuple[str, List[Symbol]]] = None, context: Any = None) -> None:
        if parts is None:
            parts = [("base", [])]
        result = self.control.ground(parts, context)
        return result

    def __getattr__(self, attr):
        if attr in self.__dict__:
            return getattr(self, attr)
        return getattr(self.control, attr)





class Observer:

    def __init__(self, program):
        self.program = program

    def rule(self, choice: bool, head: List[int], body: List[int]) -> None:
        self.program.objects.append(ClingoRule(choice=choice, head=head, body=body))

    def output_atom(self, symbol: Symbol, atom: int) -> None:
        self.program.objects.append(ClingoOutputAtom(symbol=symbol, atom=atom))

    def weight_rule(self, choice: bool, head: List[int], lower_bound: int, body: List[Tuple[int, int]]) -> None:
        self.program.objects.append(ClingoWeightRule(choice, head, body, lower_bound))

    def project(self, atoms: List[int]) -> None:
        self.program.objects.append(ClingoProject(atoms))

    def external(self, atom: int, value: TruthValue) -> None:
        self.program.objects.append(ClingoExternal(atom, value))


class Application(object):
    def __init__(self, application):
        self.application = application

    def main(self, control: clingo.Control, files: List[str]) -> None:
        control = Control(control=control)  # type: ignore
        return self.application.main(control, files)

    # def register_options(self, options: ApplicationOptions) -> None:
    #     return self.application.register_options(options)


    # def validate_options(self) -> bool:
    #     return self.application.validate_options()


    # def logger(self, code: MessageCode, message: str) -> None:
    #     return self.application.logger(code, message)


    def __getattr__(self, attr):
        if attr in self.__dict__:
            return getattr(self, attr)
        return getattr(self.application, attr)



def clingo_main(application, files: List[str] = []) -> int:  # pylint: disable=dangerous-default-value
    return clingo.clingo_main(Application(application), list(files))
