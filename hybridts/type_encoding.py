from warnings import warn
import typing as t


def add_show(cls):
    def __repr__(self):
        return cls.__name__

    cls.__repr__ = __repr__
    return cls


@add_show
class AppT:
    __slots__ = ()


app_t = AppT()


@add_show
class ArrowT:
    __slots__ = ()


arrow_t = ArrowT()


@add_show
class VarT:
    __slots__ = ()


var_t = VarT()


@add_show
class NomT:
    __slots__ = ()


nom_t = NomT()


@add_show
class FreshT:
    __slots__ = ()


fresh_t = FreshT()


@add_show
class TupleT:
    __slots__ = ()


tuple_t = TupleT()


@add_show
class ForallT:
    __slots__ = ()


forall_t = ForallT()


@add_show
class RecordT:
    __slots__ = ()


record_t = RecordT()


@add_show
class ImplicitT:
    __slots__ = ()


implicit_t = ImplicitT()


@add_show
class RowConsT:
    __slots__ = ()


row_cons_t = RowConsT()


@add_show
class RowPolyT:
    __slots__ = ()


row_poly_t = RowPolyT()


@add_show
class RowMonoT:
    __slots__ = ()


row_mono_t = RowMonoT()

a = t.NewType("a", int)

RowCons = t.Tuple[RowConsT, str, 'T', 'Row']
RowPoly = t.Tuple[RowPolyT, 'T']
RowMono = t.Tuple[RowMonoT]


def mk_row_cons(a: str, b: 'T', c: 'Row') -> 'RowCons':
    return row_cons_t, a, b, c


def mk_row_poly(a: 'T') -> 'RowPoly':
    return row_poly_t, a


def mk_row_mono() -> 'RowMono':
    return row_mono_t,


Row = t.Union[RowCons, RowPoly, RowMono]

App = t.Tuple[AppT, 'T', 'T']
Arrow = t.Tuple[ArrowT, 'T', 'T']
Var = t.Tuple[VarT, int]
Nom = t.Tuple[NomT, str]
Fresh = t.Tuple[FreshT, str]
Tuple = t.Tuple[TupleT, t.Tuple['T', ...]]
Forall = t.Tuple[ForallT, t.Tuple[str, ...], 'T']
Record = t.Tuple[RecordT, Row]
Implicit = t.Tuple[ImplicitT, 'T', 'T']

T = t.Union[App, Arrow, Var, Nom, Fresh, Tuple, Forall, Record, Implicit]


def mk_app(f: T, arg: T) -> T:
    return app_t, f, arg


def mk_arrow(arg: T, ret: T) -> T:
    return arrow_t, arg, ret


def mk_implicit(arg: T, ret: T) -> T:
    return implicit_t, arg, ret


def mk_var(i: int):
    return var_t, i


def mk_fresh(s: str):
    return fresh_t, s


def mk_tuple(*types: T):
    return (tuple_t, *types)


def mk_forall(names: t.Set[str], p: T):
    return normalize_forall(names, p)


bot: Forall = (forall_t, tuple(["a"]), (fresh_t, "a"))
empty_row: Row = (row_mono_t, )


def poly_row(ty: T):
    return row_poly_t, ty


def record_of_row(row: Row):
    return record_t, row


TypeCtx = t.Dict[int, T]

_Ctx = t.TypeVar('_Ctx')


def pre_visit(f: t.Callable[[_Ctx, T], t.Tuple[_Ctx, T]]):
    def visit_t(ctx, root: 'T') -> T:
        ctx, root = f(ctx, root)

        def eval_t(node):
            return visit_t(ctx, node)

        def eval_row(root: Row) -> Row:

            tag = root[0]
            root: Row = root
            if tag is row_cons_t:
                root: RowCons = root
                _, k, t, row = root
                return row_cons_t, k, eval_t(t), eval_row(row)
            if tag is row_mono_t:
                return root
            if tag is row_poly_t:
                root: RowPoly = root
                return row_poly_t, eval_t(root[1])
            raise TypeError(tag)

        tag = root[0]
        if tag in (var_t, nom_t, fresh_t):
            return root
        if tag is app_t:
            # must rename, due to PyCharm's weakness
            root_: App = root
            _, a, b = root_
            return app_t, eval_t(a), eval_t(b)
        if tag is arrow_t:
            root_: Arrow = root
            _, a, b = root_
            return arrow_t, eval_t(a), eval_t(b)
        if tag is tuple_t:
            root_: Tuple = root
            xs = root_[1]
            return tuple_t, tuple(map(eval_t, xs))
        if tag is implicit_t:
            root_: Implicit = root
            _, witness, t = root_
            return implicit_t, eval_t(witness), eval_t(t)
        if tag is forall_t:
            root_: Forall = root
            _, ns, t = root_
            return forall_t, ns, eval_t(t)
        if tag is record_t:
            root_: Record = root
            rowt = root_[1]
            return record_t, eval_row(rowt)
        raise TypeError(tag)

    return visit_t


def visit_check(f: t.Callable[[T], bool]):
    def eval_t(root) -> bool:
        if not f(root):
            return False

        def eval_row(root) -> bool:
            tag = root[0]
            root: Row = root
            if tag is row_cons_t:
                root: RowCons = root
                _, k, t, row = root
                return eval_t(t) and eval_row(row)
            if tag is row_mono_t:
                return True
            if tag is row_poly_t:
                root: RowPoly = root
                return eval_t(root[1])
            raise TypeError(tag)

        tag = root[0]
        if tag in (var_t, nom_t, fresh_t):
            return True
        if tag is app_t:
            # must rename, due to PyCharm's weakness
            root_: App = root
            _, a, b = root_
            return eval_t(a) and eval_t(b)
        if tag is arrow_t:
            root_: Arrow = root
            _, a, b = root_
            return eval_t(a) and eval_t(b)
        if tag is tuple_t:
            root_: Tuple = root
            xs = root_[1]
            return all(map(eval_t, xs))
        if tag is implicit_t:
            root_: Implicit = root
            _, witness, t = root_
            return eval_t(witness) and eval_t(t)
        if tag is forall_t:
            root_: Forall = root
            _, ns, t = root_
            return eval_t(t)
        if tag is record_t:
            root_: Record = root
            rowt = root_[1]
            return eval_row(rowt)
        raise TypeError(tag)

    return eval_t


def row_from_list(xs: t.List[t.Tuple[str, T]], last: Row) -> Row:
    for k, v in xs:
        last = row_cons_t, k, v, last
    return last


def row_of_map(d: t.Dict[str, T], last: Row) -> Row:
    for k, v in d.items():
        last = row_cons_t, k, v, last
    return last


class Numbering(dict):
    def __missing__(self, key):
        value = self[key] = len(self)
        return value


def normalize_forall(bounds: t.Set[str], poly):
    num = Numbering()

    def _visit_func(fresh_names: t.Set[str], ty):
        tag = ty[0]
        if tag is fresh_t:
            _, s = ty
            _ = num[s]
            return fresh_names, ty
        if tag is forall_t:
            _, ns, _ = ty
            return {n for n in fresh_names if n not in ns}, ty
        return fresh_names, ty

    left, _ = pre_visit(_visit_func)(bounds, poly)
    if left:
        warn(UserWarning("Redundant free variables {}".format(left)))

    return forall_t, (
        k for k, _ in sorted(num.items(), key=lambda x: x[1])), poly
