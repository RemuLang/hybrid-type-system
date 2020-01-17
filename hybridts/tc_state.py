from hybridts.type_encoding import *
from hybridts import tc_make
import typing as t


class TCState:
    def __init__(self, tctx: TypeCtx, structures = None):
        tc_make.make(self, tctx, structures)

    def get_tctx(self):
        raise NotImplementedError

    def get_structures(self) -> t.Dict[Var, t.Set['tc_make.StructureKeeper']]:
        raise NotImplementedError

    def occur_in(self, var: T, ty: T) -> bool:
        raise NotImplementedError

    def inst_with_structure_preserved(self, maybepoly: T, rigid=False) -> t.Tuple[t.Dict[T, Var], T]:
        raise NotImplementedError

    def inst_without_structure_preserved(self, maybepoly: T, rigid=False) -> t.Tuple[t.Dict[T, Var], T]:
        raise NotImplementedError

    def infer(self, ty: T) -> T:
        raise NotImplementedError

    def path_infer(self, ty: T) -> t.Tuple[t.Optional[Path], T]:
        """
        The first element is a type made of Var, but all of the value is most nearest one to be concrete.
        """
        raise NotImplementedError

    def unify(self, lhs: T, rhs: T) -> None:
        raise NotImplementedError

    def extract_row(self, rowt: Row) -> t.Optional[t.Dict[str, T]]:
        raise NotImplementedError

    eq_fresh: t.Dict[Fresh, Fresh]

    def copy(self):
        tcs = TCState(self.get_tctx().copy(), self.get_structures().copy())
        return tcs
