from mlftt.type_encoding import *
from mlftt import exc
from enum import Enum, auto as _auto
from collections import ChainMap
from contextlib import contextmanager
# noinspection PyUnresolvedReferences
import typing as t


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

    def _visit_func(fresh_map: dict, ty):
        tag = ty[0]
        if tag is fresh_t:
            _, s = ty
            return fresh_map, fresh_map.get(s, ty)
        if tag is forall_t:
            _, ns, _ = ty
            return {n: t for n, t in fresh_map.items() if n not in ns}, ty
        return fresh_map, ty

    def fresh(fresh_map, ty):
        return pre_visit(_visit_func)(fresh_map, ty)

    self.fresh = fresh

    def new_var():
        vid = len(tctx)
        var = var_t, vid
        tctx[vid] = var
        return var

    self.new_var = new_var

    def int_of_var(v: T) -> t.Optional[int]:
        if v[0] is var_t:
            return v[1]
        return None

    self.int_of_var = int_of_var

    def occur_in(var_id: int, ty: T) -> bool:
        if int_of_var(ty) == var_id:
            return False

        def visit_func(tt: T):
            return tt[0] is not var_t or tt[1] != var_id

        return not visit_check(visit_func)(ty)

    self.occur_in = occur_in

    def infer(x: T) -> T:
        def visit_func(_, a: T):
            if a[0] is var_t:
                i = a[1]
                b = tctx[i]
                if b[0] is var_t and b[1] == i:
                    return (), a
                b = infer(b)
                # OPT here
                if b[0] is record_t and b[1][0] is row_poly_t:
                    b = b[1][1]

                tctx[i] = b
                return (), b
            return (), a

        return pre_visit(visit_func)((), x)

    self.infer = infer

    def _extract_row(fields: t.Dict[str, T], rowt: Row) -> t.Optional[T]:
        if rowt[0] is row_cons_t:
            root: RowCons = rowt
            _, k, v, rec = root
            if k in fields:
                raise exc.RowFieldDuplicated(rowt[1])
            fields[k] = v
            return _extract_row(fields, rec)
        if rowt[0] is row_mono_t:
            return None
        if rowt[0] is row_poly_t:
            tt = rowt[1]
            if tt[0] is record_t:
                return _extract_row(fields, tt[1])
            return tt

        raise TypeError(rowt[0])

    def extract_row(rowt: Row) -> t.Tuple[t.Dict[str, T], t.Optional[T]]:
        fields = {}
        left = _extract_row(fields, rowt)
        return fields, left

    self.extract_row = extract_row

    def _unify(lhs: T, rhs: T) -> None:
        ltag = lhs[0]
        rtag = rhs[0]
        if ltag is nom_t and rtag is nom_t:
            if lhs[1] == rhs[1]:
                return
            raise exc.TypeMismatch(lhs, rhs)
        if ltag is var_t and rtag is var_t and lhs[1] == rhs[1]:
            return
        if ltag is forall_t:
            return _unify(rhs, lhs)
        if rtag is forall_t:
            rhs_matched: Forall = rhs
            _, ns, poly = rhs_matched
            fresh_map = {n: new_var() for n in ns}
            return unify(lhs, fresh(fresh_map, poly))
        if ltag is var_t:
            i = lhs[1]
            if occur_in(i, rhs):
                raise exc.IllFormedType(" a = a -> b")
            tctx[i] = rhs
            return
        if rtag is var_t:
            return _unify(rhs, lhs)

        if ltag is fresh_t:
            raise exc.UnboundTypeVar(lhs[1])

        if rtag is fresh_t:
            raise exc.UnboundTypeVar(rhs[1])

        if ltag is implicit_t and ltag is implicit_t:
            unify(lhs[1], rhs[1])
            unify(lhs[2], rhs[2])
            return

        if ltag is implicit_t:
            return unify(lhs[2], rhs)

        if rtag is implicit_t:
            return _unify(lhs, rhs[2])

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
                    return unify(row2, (record_t, record_of_map(only_by1, (row_mono_t,))))
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
                ex2 = (record_t, record_of_map(only_by1, polyrow))
                ex1 = (record_t, record_of_map(only_by2, polyrow))
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
        return _unify(lhs, rhs)

    self.unify = unify

    def redirect_side_effects(place: dict):
        @contextmanager
        def apply():
            resume = tctx
            tctx = TransactionMap(place, resume)
            try:
                yield
            finally:
                tctx = resume

        return apply

    self.redirect_side_effects = redirect_side_effects


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

    def infer(self, ty: T) -> T:
        raise NotImplementedError

    def unify(self, lhs: T, rhs: T) -> None:
        raise NotImplementedError

    def extract_row(self, rowt: Row) -> t.Optional[t.Dict[str, T]]:
        raise NotImplementedError

    def redirect_side_effects(self, place: dict):
        raise NotImplementedError

    def copy(self):
        TCState(self.get_tctx().copy())

    @classmethod
    def mk_new_type(cls, typename: str):
        return nom_t, typename

