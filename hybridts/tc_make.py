from hybridts.type_encoding import *
from hybridts import exc
from collections import defaultdict, ChainMap
import typing as t
try:
    # noinspection PyUnresolvedReferences
    from hybridts.tc_state import TCState
except ImportError:
    pass


class RowCheckFailed(Exception):
    pass


class StructureKeeper:
    is_finished: bool

    def update(self, tcs: 'TCState', path_lhs: Path) -> None:
        raise NotImplementedError


# class FlexibleStructureKeeper(StructureKeeper):
#     freshes: t.List[Fresh]
#     vars: t.List[Var]
#     fresh_pathes: t.List[T]
#     var_paths: t.List[T]
#     is_finished: bool
#
#     def __init__(self, freshes: t.List[Fresh], vars: t.List[Var],
#                  fresh_pathes: t.List[T], var_paths: t.List[T]):
#         self.freshes = freshes
#         self.vars = vars
#         self.fresh_pathes = fresh_pathes
#         self.var_paths = var_paths
#         self.is_finished = False
#
#     def __repr__(self):
#         # TODO
#         return 'FlexibleStructure({!r} = {!r} ~ {!r} = {!r})'.format(
#             self.freshes, self.fresh_pathes, self.vars, self.var_paths)
#
#     def update(self, tcs: 'TCState', path_lhs: Path) -> None:
#         var_paths = tuple(tcs.path_infer(path)[0] for path in self.var_paths)
#         fresh_paths = tuple(
#             tcs.path_infer(path)[0] for path in self.fresh_pathes)
#
#         lookup = {k: v for k, v in zip(fresh_paths, self.freshes)}
#
#         def subst(_, t):
#             return (), lookup.get(t, t)
#
#         vars_path_tp = Tuple(var_paths)
#         vars_path_tp = pre_visit(subst)((), tcs.infer(vars_path_tp))
#
#         for var, each in zip(self.vars, vars_path_tp.elts):
#             tcs.unify(var, each)
#
#         vars_ftv = ftv(vars_path_tp)
#         if not vars_ftv:
#             self.is_finished = True
#         # TODO:
#         # forall a. a -> var
#         # unify with ('i -> 'j) -> ('j -> 'i), where
#         #     'i, 'j are variables,
#         # this certainly can be true, unless
#         #   infer(i') != infer('j)   and
#         #   infer(i') = some non-var and
#         #   infer(j') = some non-var
#
#         else:
#             # fresh_paths_ftv = ftv(Tuple(fresh_paths))
#             # if fresh_paths_ftv.issuperset(vars_ftv):
#             #     raise exc.StructureCannotUnify(vars)
#             path_lhs, _ = tcs.path_infer(path_lhs)
#             structures = tcs.get_structures()
#             for fv in ftv(path_lhs):
#                 structures[fv].add(self)

# class RigidStructureKeeper(StructureKeeper):
#     template: T
#     path: T
#     is_finished: bool
#
#     def __init__(self, template: T, path: T):
#         self.template = template
#         self.path = path
#         self.is_finished = False
#
#     def __repr__(self):
#         return 'RigidStructure({!r} = {!r})'.format(self.template, self.path)
#
#     def update(self, tcs: 'TCState', path_lhs: Path) -> None:
#         path, _ = tcs.path_infer(self.path)
#         _, structure = fresh_ftv(path)
#
#         tcs.unify(structure, self.template)
#
#         if not ftv(tcs.infer(self.template)):
#             self.is_finished = True
#         else:
#             path_lhs, _ = tcs.path_infer(path_lhs)
#             structures = tcs.get_structures()
#             for fv in ftv(path_lhs):
#                 structures[fv].add(self)


def update(tcs: 'TCState', bounds, vars, freshed_bounds, freshed_vars) -> None:

    left = Tuple(bounds + vars)
    right = Tuple(freshed_bounds + freshed_vars)
    path, _ = tcs.path_infer(right)
    rev_map, structure = fresh_ftv(path)
    tcs.unify(left, structure)

    ftv_vars = ftv(tcs.infer(structure))
    if ftv_vars:
        resume = {tcs.infer(v): k for k, v in rev_map.items()}
        for ftv_var in ftv_vars:
            tcs.unify(resume[ftv_var], ftv_var)


def make(self: 'TCState', tctx: TypeCtx,
         structures: t.Dict[Var, t.Set[StructureKeeper]]):

    # fresh variables are guaranteed to be not free due to syntax restriction of forall
    #  thus, when proceeding unification, freshvar cannot be greater or lesser than
    #  any other type except another fresh variable.
    # However, fresh variable can only equal to another by a bidirectional name mapping

    structures: t.Dict[Var,
                       t.Set[StructureKeeper]] = structures or defaultdict(set)
    self.get_tctx = lambda: tctx

    # key => [(template, path)]
    # every time, `path` gets updatd, we fresh all type variables in `path`, which
    # produces a closed new type, and use this unify with `template`

    def subst_once(subst_map: t.Dict[T, T], ty):
        return subst_map, subst_map.get(ty, ty)

    def subst(subst_map: t.Dict[T, T], ty: T):
        return pre_visit(subst_once)(subst_map, ty)

    def occur_in(var: T, ty: T) -> bool:
        if var is ty:
            return False

        def visit_func(tt: T):
            return not isinstance(tt, Var) or tt is not var

        return not visit_check(visit_func)(ty)

    def infer_row(x: Row) -> t.Tuple[t.Optional[Row], Row]:
        if isinstance(x, RowCons):
            field_path, field_t = path_infer(x.field_type)
            tl_path, tl_t = infer_row(x.tail)
            if field_path and tl_path:
                path = RowCons(x.field_name, field_path, tl_path)
            else:
                path = None
            return path, RowCons(x.field_name, field_t, tl_t)
        if isinstance(x, RowMono):
            return None, x
        if isinstance(x, RowPoly):
            path_p, t_p = path_infer(x.type)
            if path_p:
                path = RowPoly(path_p)
            else:
                path = None
            return path, RowPoly(t_p)
        raise TypeError(x)

    def path_infer(x: T) -> t.Tuple[t.Optional[Path], T]:
        if isinstance(x, Nom):
            return None, x

        if isinstance(x, Var):
            path_end = tctx.get(x)
            if not path_end:
                return x, x
            path_x, end = path_end
            path_y, y = path_infer(end)
            path, end = tctx[x] = (path_y or path_x or x), y
            if x.is_rigid and not isinstance(end, LeafTypes):
                raise exc.RigidTypeExpanding(x)

            return path, end

        if isinstance(x, Fresh):
            return x, x

        if isinstance(x, App):
            f_path, f_t = path_infer(x.f)
            arg_path, arg_t = path_infer(x.arg)
            if f_path and arg_path:
                path = App(f_path, arg_path)
            else:
                path = None
            return path, App(f_t, arg_t)
        if isinstance(x, Arrow):
            ret_path, ret_t = path_infer(x.ret)
            arg_path, arg_t = path_infer(x.arg)
            if ret_path and arg_path:
                path = Arrow(arg_path, ret_path)
            else:
                path = None
            return path, Arrow(arg_t, ret_t)
        if isinstance(x, Implicit):
            arg_path, arg_t = path_infer(x.witness)
            ret_path, ret_t = path_infer(x.type)
            if ret_path and arg_path:
                path = Implicit(arg_path, ret_path)
            else:
                path = None
            return path, Implicit(arg_t, ret_t)
        if isinstance(x, Tuple):
            if not x.elts:
                return None, x
            paths, ts = zip(*map(path_infer, x.elts))
            if all(paths):
                path = Tuple(paths)
            else:
                path = None
            return path, Tuple(ts)
        if isinstance(x, Forall):
            poly_path, poly_t = path_infer(x.poly_type)
            if poly_path:
                path = Forall(x.token, x.fresh_vars, poly_path)
            else:
                path = None
            return path, Forall(x.token, x.fresh_vars, poly_t)
        if isinstance(x, Record):
            path_row, row_t = infer_row(x.row)
            if not path_row:
                path = None
            else:
                path = Record(path_row)

            if isinstance(path_row, RowPoly):
                path = path_row.type

            if isinstance(row_t, RowPoly):
                type = row_t.type
            else:
                type = Record(row_t)

            return path, type
        raise TypeError(x)

    def inst_forall_with_structure_preserved(bound_vars: t.Iterable[Fresh],
                                             polytype: T):
        mapping: t.Dict[T, Var] = {
            b: InternalVar(is_rigid=True)
            for b in bound_vars
        }
        vars: t.Dict[Var, Var] = {}
        chain = ChainMap(vars, mapping)
        # forall a. var -> a
        # forall b. b -> b
        # var -> i
        # j -> j
        _, monotype = fresh_ftv(polytype, chain)
        # lhs, rhs = zip(*mapping.items())
        # assert mapping
        # structure_keeper = RigidStructureKeeper(Tuple(lhs), Tuple(rhs))
        # for each in rhs:
        #     structures[each].add(structure_keeper)
        return mapping, vars, monotype

    # def inst_with_structure_preserved(type,
    #                                   rigid=False
    #                                   ) -> t.Tuple[t.Dict[T, Var], T]:
    #     if isinstance(type, Forall):
    #         poly_type = type.poly_type
    #         if rigid:
    #             mapping: t.Dict[T, Var] = {b: InternalVar(is_rigid=True) for b in type.fresh_vars}
    #             _, poly_type = just_fresh_bounds(poly_type, mapping)
    #             if mapping:
    #                 lhs, rhs = zip(*mapping.items())
    #                 structure_keeper = RigidStructureKeeper(
    #                     Tuple(lhs), Tuple(rhs))
    #                 for each in rhs:
    #                     structures[each].add(structure_keeper)
    #         else:
    #             mapping: t.Dict[T, Var] = {b: InternalVar(is_rigid=False) for b in type.fresh_vars}
    #             _, poly_type = just_fresh_bounds(poly_type, mapping)
    #
    #             vars = {}
    #             freshes = {}
    #             for k, v in mapping.items():
    #                 if isinstance(k, Var):
    #                     kv = vars
    #                 else:
    #                     assert isinstance(k, Fresh)
    #                     kv = freshes
    #                 kv[k] = v
    #             if not vars:
    #                 return mapping, poly_type
    #
    #             freshes, fresh_paths = zip(*freshes.items())
    #             vars, var_paths = zip(*vars.items())
    #             structure_keeper = FlexibleStructureKeeper(
    #                 list(freshes), list(vars), list(fresh_paths),
    #                 list(var_paths))
    #             for each in mapping.values():
    #                 structures[each].add(structure_keeper)
    #         type = poly_type
    #     else:
    #         mapping = {}
    #     return mapping, type

    def inst_without_structure_preserved(type) -> t.Tuple[t.Dict[T, Var], T]:
        """
        When using this, there should be no free variable in the scope of forall!
        """
        if isinstance(type, Forall):
            mapping: t.Dict[T, Var] = {
                b: InternalVar(is_rigid=False)
                for b in type.fresh_vars
            }
            type = type.poly_type
            _, type = just_fresh_bounds(type, mapping)
            return mapping, type
        return {}, type

    def _unify(lhs: T, rhs: T, path_lhs: Path, path_rhs: Path) -> None:
        if lhs is rhs:
            # Nom, Fresh, Var
            return

        if isinstance(lhs, Var):
            if occur_in(lhs, rhs):
                raise exc.IllFormedType(" a = a -> b")
            if lhs.is_rigid:
                if not isinstance(rhs, LeafTypes):
                    raise exc.TypeMismatch(lhs, rhs)
            path_rhs, _ = path_infer(rhs)
            tctx[lhs] = (path_rhs or path_lhs), rhs
            structure_keepers = structures.get(lhs)
            if structure_keepers:
                for structure_keeper in tuple(structure_keepers):
                    if structure_keeper.is_finished:
                        structure_keepers.remove(structure_keeper)
                        continue
                    else:
                        structure_keeper.update(self, path_lhs)
            return

        if isinstance(rhs, Var):
            return _unify(rhs, lhs, path_rhs, path_lhs)

        if isinstance(lhs, Forall) and isinstance(rhs, Forall):
            freshes_l, vars_l, l_p = inst_forall_with_structure_preserved(
                lhs.fresh_vars, lhs.poly_type)
            freshes_r, vars_r, r_p = inst_forall_with_structure_preserved(
                rhs.fresh_vars, rhs.poly_type)
            unify(l_p, r_p)
            if vars_l:
                a, b = zip(*freshes_l.items())
                c, d = zip(*vars_l.items())
                update(self, a, c, b, d)
            if vars_r:
                a, b = zip(*freshes_r.items())
                c, d = zip(*vars_r.items())
                update(self, a, c, b, d)
            return

        if isinstance(lhs, Implicit) and isinstance(rhs, Implicit):
            unify(lhs.witness, rhs.witness)
            unify(lhs.type, rhs.type)
            return

        if isinstance(lhs, Implicit):
            return unify(lhs.type, rhs)

        if isinstance(rhs, Implicit):
            return unify(lhs, rhs.type)

        if isinstance(lhs, Fresh) and isinstance(rhs, Fresh):
            if lhs.token is rhs.token and lhs.name == rhs.name:
                return
            raise exc.TypeMismatch(lhs, rhs)
        if isinstance(lhs, Arrow) and isinstance(rhs, Arrow):
            unify(lhs.arg, rhs.arg)
            unify(lhs.ret, rhs.ret)
            return

        if isinstance(lhs, App) and isinstance(rhs, App):
            unify(lhs.f, rhs.f)
            unify(lhs.arg, rhs.arg)
            return

        if isinstance(lhs, Tuple) and isinstance(rhs, Tuple):
            for a, b in zip(lhs.elts, rhs.elts):
                unify(a, b)
            return

        if isinstance(lhs, Record) and isinstance(rhs, Record):
            m1, ex1 = extract_row(lhs.row)
            m2, ex2 = extract_row(rhs.row)
            common_keys = m1.keys() & m2.keys()
            only_by1 = {k: v for k, v in m1.items() if k not in common_keys}
            only_by2 = {k: v for k, v in m2.items() if k not in common_keys}

            for k in common_keys:
                unify(m1[k], m2[k])

            def row_check(row1, row2, only_by1, only_by2):
                if row1 is None and row2 is None:
                    if only_by1 or only_by2:
                        raise RowCheckFailed
                    return
                if row2 is None:
                    return row_check(row2, row1, only_by2, only_by1)
                if row1 is None:
                    # only_by1 == {only_by2 | row2}
                    #  where
                    #    only_by1 \cap only_by2 = \emptyset,
                    #  therefore,
                    #    only_by2 = \emptyset,
                    #    row2 = only_by1
                    if only_by2:
                        raise RowCheckFailed
                    return unify(row2, Record(row_of_map(only_by1, empty_row)))
                # {only_by1|row1} == {only_by2|row2},
                # where
                #   only_by1 \cap only_by2 = \emptyset,
                # therefore,
                #   forall type in only_by2. type in row1, and
                #   forall type in only_by1. type in row2,
                # therefore,
                #   t1 = {only_by1 \cup only_by2|row} = t2,
                #   {only_by1|row} = row2
                #   {only_by2|row} = row1
                polyrow = RowPoly(InternalVar(is_rigid=False))
                ex2 = Record(row_of_map(only_by1, polyrow))
                ex1 = Record(row_of_map(only_by2, polyrow))
                unify(row1, ex1)
                unify(row2, ex2)

            try:
                return row_check(ex1, ex2, only_by1, only_by2)
            except RowCheckFailed:
                raise exc.TypeMismatch(lhs, rhs)
        raise exc.TypeMismatch(lhs, rhs)

    def unify(lhs, rhs):

        path_lhs, lhs = path_infer(lhs)
        path_rhs, rhs = path_infer(rhs)
        _unify(lhs, rhs, path_lhs, path_rhs)

    def infer(t):
        return path_infer(t)[1]

    # self.inst_with_structure_preserved = inst_with_structure_preserved
    self.inst_without_structure_preserved = inst_without_structure_preserved
    self.unify = unify
    self.path_infer = path_infer
    self.occur_in = occur_in
    self.extract_row = extract_row
    self.infer = infer
    self.get_structures = lambda: structures
