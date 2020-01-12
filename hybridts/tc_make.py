from hybridts.type_encoding import *
from hybridts import exc

import typing as t
try:
    # noinspection PyUnresolvedReferences
    from hybridts.tc_state import TCState
except ImportError:
    pass


class RowCheckFailed(Exception):
    pass


def make(self: 'TCState', tctx: TypeCtx):

    # fresh variables are guaranteed to be not free due to syntax restriction of forall
    #  thus, when proceeding unification, freshvar cannot be greater or lesser than
    #  any other type except another fresh variable.
    # However, fresh variable can only equal to another by a bidirectional name mapping

    self.get_tctx = lambda: tctx
    self.eq_fresh = None

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
            if x.topo_maintainers:
                topo = x.topo_maintainers
                for each in topo:
                    each.update(x)

                if topo:

                    def transfer_topo_notifier_to_all_path_type_vars(tt: T):
                        if isinstance(tt, Var):
                            tt.topo_maintainers.update(topo)
                        return True

                    if path:
                        visit_check(
                            transfer_topo_notifier_to_all_path_type_vars)(path)

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
            paths, ts = zip(*map(path_infer, x.elts))
            if all(paths):
                path = Tuple(paths)
            else:
                path = None
            return path, Tuple(ts)
        if isinstance(x, Forall):
            poly_path, poly_t = path_infer(x.poly_type)
            if poly_path:
                path = Forall(x.scope, x.fresh_vars, poly_path)
            else:
                path = None
            return path, Forall(x.scope, x.fresh_vars, poly_t)
        if isinstance(x, Record):
            path_row, row_t = infer_row(x.row)
            if not path_row:
                path = None
            else:
                path = Record(path_row)
            return path, Record(row_t)
        raise TypeError(x)

    def _extract_row(fields: t.Dict[str, T], rowt: Row) -> t.Optional[T]:
        if isinstance(rowt, RowCons):
            field_name = rowt.field_name
            if field_name in fields:
                raise exc.RowFieldDuplicated(field_name)
            fields[field_name] = rowt.field_type
            return _extract_row(fields, rowt.tail)
        if isinstance(rowt, RowMono):
            return None
        if isinstance(rowt, RowPoly):
            tt = rowt.type
            if isinstance(tt, Record):
                return _extract_row(fields, tt.row)
            return tt

        raise TypeError(rowt)

    def extract_row(rowt: Row) -> t.Tuple[t.Dict[str, T], t.Optional[T]]:
        fields = {}
        left = _extract_row(fields, rowt)
        return fields, left

    def rigid_inst(fresh_vars: t.Tuple[Fresh, ...], poly: T):
        mapping = {each: InternalVar(is_rigid=True) for each in fresh_vars}
        return subst(mapping, poly)

    def flexible_inst(fresh_vars: t.Tuple[Fresh, ...], poly: T):
        mapping = {each: InternalVar(is_rigid=False) for each in fresh_vars}
        return subst(mapping, poly)

    def auto_inst(mapping: t.Dict[T, T], poly: T):
        """not invoked by user
        """
        def rec_mk_world(subst_map: t.Dict[T, T], old_world_t):
            new_world_t = subst_map.get(old_world_t)
            if not new_world_t:
                if isinstance(old_world_t, Var):
                    new_world_t = subst_map[old_world_t] = InternalVar(
                        old_world_t.is_rigid)
                else:
                    new_world_t = old_world_t
            return new_world_t

        return pre_visit(rec_mk_world)(mapping, poly)

    def _unify(lhs: T, rhs: T) -> None:

        if lhs is rhs:
            # Nom, Fresh, Var
            return

        if isinstance(lhs, Var):
            if occur_in(lhs, rhs):
                raise exc.IllFormedType(" a = a -> b")
            if lhs.is_rigid:
                if not isinstance(rhs, LeafTypes):
                    raise exc.TypeMismatch(lhs, rhs)
            tctx[lhs] = rhs, rhs
            return

        if isinstance(rhs, Var):
            return _unify(rhs, lhs)

        if isinstance(lhs, Forall):
            if isinstance(rhs, Forall):
                if lhs.scope is rhs.scope:
                    return
                else:
                    K = {
                        e: InternalVar(is_rigid=True)
                        for e in lhs.fresh_vars + rhs.fresh_vars
                    }
                    l_p = auto_inst(K, lhs.poly_type)
                    r_p = auto_inst(K, rhs.poly_type)
            else:
                K = {e: InternalVar(is_rigid=True) for e in lhs.fresh_vars}
                l_p = lhs.poly_type
                r_p = rhs

            vars = set()

            for k, _ in K.items():
                if isinstance(k, Var):
                    vars.add(k)

            if not vars:
                # no break, no type variable in l_p or r_p
                tmp, self.eq_fresh = self.eq_fresh, set()
                unify(l_p, r_p)
                self.eq_fresh = tmp
                return

            local_type_topo = LocalTypeTypo(K, self)
            for var in vars:
                var.topo_maintainers.add(local_type_topo)
            local_type_topo.inner_universe.unify(l_p, r_p)

            # noinspection PyUnboundLocalVariable
            local_type_topo.update(var)  # must have been assigned, please.

        if isinstance(rhs, Forall):
            _unify(rhs, lhs)

        if isinstance(lhs, Fresh) and isinstance(rhs, Fresh):
            eq_fresh = self.eq_fresh
            if not eq_fresh:
                return

            lhs, rhs = sorted((lhs, rhs))
            look_l = eq_fresh.get(lhs)
            if look_l:
                if look_l is rhs:
                    return
                raise exc.TypeMismatch(lhs, rhs)

            eq_fresh[lhs] = rhs
            return

        if isinstance(lhs, Implicit) and isinstance(rhs, Implicit):
            unify(lhs.witness, rhs.witness)
            unify(lhs.type, rhs.type)
            return

        if isinstance(lhs, Implicit):
            return unify(lhs.type, rhs)

        if isinstance(rhs, Implicit):
            return unify(lhs, rhs.type)

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
        _, lhs = path_infer(lhs)
        _, rhs = path_infer(rhs)

        _unify(lhs, rhs)

    def infer(t):
        return path_infer(t)[1]

    def inst(t, rigid=False):
        if isinstance(t, Forall):
            if rigid:
                return rigid_inst(t.fresh_vars, t.poly_type)

            return flexible_inst(t.fresh_vars, t.poly_type)
        return t


    self.inst = inst
    self.unify = unify
    self.path_infer = path_infer
    self.occur_in = occur_in
    self.extract_row = extract_row
    self.infer = infer
