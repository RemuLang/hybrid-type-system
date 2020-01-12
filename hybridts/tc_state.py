from hybridts.type_encoding import *
from hybridts.tc_make import make
# noinspection PyUnresolvedReferences
import typing as t



class TCState:
    def __init__(self, tctx: TypeCtx):
        make(self, tctx)

    def get_tctx(self):
        raise NotImplementedError

    def get_all_vars(self):
        raise NotImplementedError

    def fresh(self, fresh_map: t.Dict[str, T], ty: T) -> T:
        raise NotImplementedError

    def register_var(self, var: Var) -> None:
        """
        When using a type variable in a type state, you're
        expected to register it first if it's not allocated
        by TCState.new_var
        """
        raise NotImplementedError

    def new_var(self, is_rigid: bool) -> T:
        raise NotImplementedError

    def occur_in(self, var: T, ty: T) -> bool:
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


class LocalTypeTypo:
    outers: t.Tuple[T, ...]
    inners: t.Tuple[T, ...]

    inner_universe: TCState
    outer_universe: TCState

    def __init__(self, K: t.Dict[T, T], outer_universe: TCState):
        self.inner_universe = TCState({})
        self.outer_universe = outer_universe

        (self.outers, self.inners) = zip(*((k, v) for k, v in K.items()))

    @staticmethod
    def _universe_update(u1: TCState, tps1: t.Tuple[T, ...], u2: TCState,
                         tps2: t.Tuple[T, ...]):
        subst_map: t.Dict[Var, Var] = {}

        def subst(_, outer_v: T):
            if isinstance(outer_v, Var):
                inner_v = subst_map.get(outer_v, None)
                if inner_v:
                    return inner_v
                return (), u2.new_var(outer_v.is_rigid)
            return (), outer_v

        for tp1, tp2 in zip(tps1, tps2):
            tp1_t = u1.infer(tp1)
            tp2_t = pre_visit(subst)((), tp1_t)
            u2.unify(tp2_t, tp2)
        return subst_map

    def update(self):
        if not self._universe_update(self.outer_universe, self.outers, self.inner_universe, self.inners):
            # all type variables of this topology are solved
            # this universe is going to the end.
            for each in self.outers:
                each.topo_maintainers.remove(self)
            return

        self._universe_update(self.inner_universe, self.inners, self.outer_universe, self.outers)
