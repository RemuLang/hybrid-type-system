from hybridts.type_encoding import *
from hybridts.tc_make import make
# noinspection PyUnresolvedReferences
import typing as t



class TCState:
    def __init__(self, tctx: TypeCtx):
        make(self, tctx)

    def get_tctx(self):
        raise NotImplementedError

    def fresh(self, fresh_map: t.Dict[str, T], ty: T) -> T:
        raise NotImplementedError

    def new_var(self) -> T:
        raise NotImplementedError

    def int_of_var(self, ty: T) -> t.Optional[int]:
        raise NotImplementedError

    def occur_in(self, var_id: int, ty: T) -> bool:
        raise NotImplementedError

    def inst(self, poly: T) -> T:
        raise NotImplementedError

    def infer(self, ty: T) -> T:
        raise NotImplementedError

    def unify(self, lhs: T, rhs: T) -> None:
        raise NotImplementedError

    def extract_row(self, rowt: Row) -> t.Optional[t.Dict[str, T]]:
        raise NotImplementedError

    def redirect_side_effects(self, place: dict):
        raise NotImplementedError

    def finish(self):
        raise NotImplementedError

    def copy(self):
        TCState(self.get_tctx().copy())

    @classmethod
    def mk_new_type(cls, typename: str):
        return nom_t, typename


class LocalTypeTypo:
    Klhs: t.Set[t.Tuple[T, T]]
    Krhs: t.Set[t.Tuple[T, T]]

    universe: TCState
