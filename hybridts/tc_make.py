from hybridts.type_encoding import *
from hybridts import exc
from collections import ChainMap
from contextlib import contextmanager

import typing as t
try:
    # noinspection PyUnresolvedReferences
    from hybridts.tc_state import TCState
except ImportError:
    pass


# noinspection PyUnresolvedReferences
class TransactionMap(ChainMap):
    def __setitem__(self, key, value):
        self.maps[0][key] = value

    def __delitem__(self, key):
        del self.maps[0][key]


class RowCheckFailed(Exception):
    pass


def make(self: 'TCState', tctx: TypeCtx):
    self.get_tctx = lambda: tctx

    # fresh variables are guaranteed to be not free due to syntax restriction of forall
    #  thus, when proceeding unification, freshvar cannot be greater or lesser than
    #  any other type except another fresh variable.
    # However, fresh variable can only equal to another by a bidirectional name mapping

    def subst_once(subst_map: t.Dict[T, T], ty):
        return subst_map.get(ty, ty)

    def subst(subst_map: t.Dict[T, T], ty: T):
        return pre_visit(subst_once)(subst_map, ty)

    def new_var(is_rigid=False):
        return InternalVar(is_rigid)

    self.new_var = new_var

    def occur_in(var: T, ty: T) -> bool:
        if var is ty:
            return False

        def visit_func(tt: T):
            return not isinstance(tt, Var) or tt is not var

        return not visit_check(visit_func)(ty)

    def infer(x: T) -> T:
        def visit_func(_, a: T):
            if isinstance(a, Var):
                b = tctx.get(a)
                if not b:
                    return (), a
                b = infer(b)
                if isinstance(b, Record):
                    tail = b.row.tail
                    if isinstance(tail, RowPoly):
                        b = tail

                tctx[a] = b
                return (), b
            return (), a

        return pre_visit(visit_func)((), x)

    self.infer = infer

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

    def _unify(lhs: T, rhs: T, once_manager: OnceManager) -> None:
        ltag = lhs[0]
        rtag = rhs[0]
        if ltag is once_t and rtag is once_t:
            if lhs[1].contents or rhs[1].contents:
                raise OnceTypeMismatch
            if lhs[1] is rhs[1]:
                return
            raise OnceTypeMismatch

        if ltag is nom_t and rtag is nom_t:
            if lhs[1] == rhs[1]:
                return
            raise exc.TypeMismatch(lhs, rhs)
        if ltag is var_t and rtag is var_t and lhs[1] == rhs[1]:
            return

        if ltag is var_t:
            i = lhs[1]
            if occur_in(i, rhs):
                raise exc.IllFormedType(" a = a -> b")
            tctx[i] = rhs
            return

        if rtag is var_t:
            return _unify(rhs, lhs, once_manager)

        if ltag is forall_t and rtag is forall_t:
            # must be normalized!
            # don't check here
            _, ns1, p1 = lhs
            _, ns2, p2 = rhs
            if len(ns1) != len(ns2):
                raise exc.TypeMismatch(lhs, rhs)

            # use `if ns1 == ns2` here? my data is immutable, seems
            # will improve performance?
            return unify(fresh(dict(zip(ns1, ns2)), p1), p2)

        if ltag is forall_t:
            _, ns, p = lhs
            lt = fresh({n: once_manager.allocate() for n in ns}, p)
            return unify(lt, rhs)

        if rtag is forall_t:
            return _unify(rhs, lhs, once_manager)

        if ltag is fresh_t and rtag is fresh_t:
            # there's only one forall context.
            # Fresh types from other forall types will be freshed to types like
            #   (t >= bound)
            # , or
            #   (t = bound)
            # , where bound is closed.
            return lhs[1] == rhs[1]

        if ltag is implicit_t and ltag is implicit_t:
            unify(lhs[1], rhs[1])
            unify(lhs[2], rhs[2])
            return

        if ltag is implicit_t:
            return unify(lhs[2], rhs)

        if rtag is implicit_t:
            return unify(lhs, rhs[2])

        if ltag is arrow_t and rtag is arrow_t:
            unify(lhs[1], rhs[1])
            unify(lhs[2], rhs[2])
            return

        if ltag is app_t and rtag is app_t:
            unify(lhs[1], rhs[1])
            unify(lhs[2], rhs[2])
            return

        if ltag is tuple_t and rtag is tuple_t:
            for a, b in zip(lhs[1], rhs[1]):
                unify(a, b)
            return

        if ltag is record_t and rtag is record_t:
            m1, ex1 = extract_row(lhs[1])
            m2, ex2 = extract_row(rhs[1])
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
                    return unify(row2,
                                 (record_t, row_of_map(only_by1,
                                                       (row_mono_t, ))))
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
                polyrow = (row_poly_t, new_var())
                ex2 = (record_t, row_of_map(only_by1, polyrow))
                ex1 = (record_t, row_of_map(only_by2, polyrow))
                unify(row1, ex1)
                unify(row2, ex2)

            try:
                return row_check(ex1, ex2, only_by1, only_by2)
            except RowCheckFailed:
                raise exc.TypeMismatch(lhs, rhs)
        raise exc.TypeMismatch(lhs, rhs)

    def unify(lhs, rhs):
        lhs = infer(lhs)
        rhs = infer(rhs)
        manager = OnceManager()
        closer = manager.start()
        try:
            _unify(lhs, rhs, once_manager=manager)
        except OnceTypeMismatch:
            raise exc.TypeMismatch(infer(lhs), infer(rhs))
        finally:
            if closer:
                closer()

    self.unify = unify

    def redirect_side_effects(place: dict):
        @contextmanager
        def apply():
            nonlocal tctx
            resume = tctx
            tctx = TransactionMap(place, resume)
            try:
                yield
            finally:
                tctx = resume

        return apply

    self.redirect_side_effects = redirect_side_effects
