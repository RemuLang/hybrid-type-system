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

    def occur_in(self, var: T, ty: T) -> bool:
        raise NotImplementedError

    def inst(self, poly: T) -> T:
        raise NotImplementedError

    def infer(self, ty: T) -> t.Tuple[t.Optional[Path], T]:
        """
        The first element is a type made of Var, but all of the value is most nearest one to be concrete.
        """
        raise NotImplementedError

    def unify(self, lhs: T, rhs: T) -> None:
        raise NotImplementedError

    def extract_row(self, rowt: Row) -> t.Optional[t.Dict[str, T]]:
        raise NotImplementedError

    def set_eq_fresh(self, local_fresh_eqs: t.Set[t.Set[T]]) -> None:
        raise NotImplementedError

    def copy(self):
        return TCState(self.get_tctx().copy())


class LocalTypeTypo:
    # the keys and values(K, J) are all paths
    K: t.Dict[T, T]  # outer to inner
    J: t.Dict[T, T]  # inner to outer

    local_fresh_eqs: t.Set[t.Set[T]]  # equivalent fresh variables
    inner_universe: TCState
    outer_universe: TCState

    def __init__(self, K: t.Dict[T, T], outer_universe: TCState):
        self.dirty = False
        self.inner_universe = TCState({})
        self.outer_universe = outer_universe
        self.K = K
        self.J = {v: K for k, v in K.items()}
        self.local_fresh_eqs = set()

    @staticmethod
    def _universe_update(u1: TCState, u2: TCState, tps: t.Dict[T, T], rev_tps: t.Dict[T, T]):
        subst_map: t.Dict[Var, Var] = {}

        def subst(_, v1: T):
            v2 = tps.get(v1)
            if v2:
                return (), v2
            if isinstance(v1, Var):
                v2 = subst_map.get(v1)
                if v2:
                    return (), v2
                v2 = subst_map[v1] = InternalVar(v2.is_rigid)

                return (), v2
            return (), v1

        for u1_t0, u2_t0 in tps.items():
            # t u1   <-->   t from universe 2
            #  |   step 1 -->           step 2
            # \|/ pruned         /|\  unify
            # t u1'  <-->   t' from universe 2
            u2_t0 = tps[u1_t0]
            u1_t1, no_path_t = u1.infer(u1_t0)
            assert u1_t1
            u2_t1 = tps.get(u1_t1)
            if not u2_t1:
                u2_t1 = tps[u1_t1] = pre_visit(subst)((), u1_t1)
                rev_tps[u2_t1] = u1_t1

            u2.unify(u2_t0, u2_t1)

    def update(self, var: T):
        if self.dirty:
            var.topo_maintainers.remove(self)
            return
        self.outer_universe.set_eq_fresh(self.local_fresh_eqs)
        self._universe_update(self.outer_universe, self.inner_universe, self.K, self.J)
        self._universe_update(self.inner_universe, self.outer_universe, self.J, self.K)
        self._final_check()

    def _final_check(self):
        inner_infer = self.inner_universe.infer
        _, all_keys = {inner_infer(key)[1] for key in self.K}

        def check_if_no_type_var(v1: T):
            return not isinstance(v1, Var)

        if all(map(visit_check(check_if_no_type_var), all_keys)):
            self.dirty = True
