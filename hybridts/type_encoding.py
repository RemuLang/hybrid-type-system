from warnings import warn
from typing_extensions import Protocol
import abc
import typing as t
from dataclasses import dataclass

try:
    # noinspection PyUnresolvedReferences
    from hybridts.tc_state import LocalTypeTypo
except ImportError:
    pass


@dataclass(eq=True, frozen=True, order=True)
class Fresh:
    name: str
    scope: 'ForallGroup'


class ForallGroup(Protocol):
    def get_names(self) -> t.Protocol[Fresh]:
        ...


class Var:
    @property
    def is_rigid(self) -> bool:
        raise NotImplementedError

    @property
    def topo_maintainers(self) -> t.Set['LocalTypeTypo']:
        raise NotImplementedError


class InternalVar(Var):
    """
    This kind of type variable is not user-created, but you does can,
    if you don't mind the bad error reporting :)
    """
    is_rigid: bool
    topo_maintainers: t.Set[t.Tuple['T', 'LocalTypeTypo']]

    def __init__(self, is_rigid: bool):
        self.topo_maintainers = set()
        self.is_rigid = is_rigid


G = t.TypeVar('G')


class Ref(t.Generic[G]):

    contents: G

    def __init__(self, contents: G):
        self.contents = contents


@dataclass(eq=True, frozen=True, order=True)
class RowCons:
    field_name: str
    field_type: 'T'
    tail: 'Row'


@dataclass(eq=True, frozen=True, order=True)
class RowPoly:
    type: 'T'


@dataclass(eq=True, frozen=True, order=True)
class RowMono:
    pass


empty_row = RowMono()

Row = t.Union[RowCons, RowPoly, RowMono]


@dataclass(eq=True, frozen=True, order=True)
class App:
    f: 'T'
    arg: 'T'


@dataclass(eq=True, frozen=True, order=True)
class Arrow:
    arg: 'T'
    ret: 'T'


class Nom(abc.ABC):
    @abc.abstractmethod
    def get_name(self) -> str:
        raise NotImplementedError


@dataclass(eq=True, frozen=True, order=True)
class Tuple:
    elts: t.Tuple['T', ...]


@dataclass(eq=True, frozen=True, order=True)
class Forall:
    scope: ForallGroup
    fresh_vars: t.Tuple[Fresh, ...]
    poly_type: 'T'


@dataclass(eq=True, frozen=True, order=True)
class Record:
    row: Row


@dataclass(eq=True, frozen=True, order=True)
class Implicit:
    witness: 'T'
    type: 'T'


@dataclass(eq=True, frozen=True, order=True)
class UnboundFresh:
    n: str


T = t.Union[App, Arrow, Var, Nom, Fresh, Tuple, Forall, Record, Implicit]

TypeCtx = t.Dict[Var, T]
Handler = t.Callable

_Ctx = t.TypeVar('_Ctx')

LeafTypes = (Var, Nom, Fresh, UnboundFresh)


def pre_visit(f: t.Callable[[_Ctx, T], t.Tuple[_Ctx, T]]):
    def visit_t(ctx, root: 'T') -> T:
        ctx, root = f(ctx, root)

        def eval_t(node):
            return visit_t(ctx, node)

        def eval_row(root: Row) -> Row:
            if isinstance(root, RowCons):
                return RowCons(root.field_name, eval_t(root.field_type),
                               eval_row(root.tail))
            if isinstance(root, RowMono):
                return root

            if isinstance(root, RowPoly):
                return RowPoly(eval_t(root.type))
            raise TypeError(root)

        if isinstance(root, LeafTypes):
            return root

        if isinstance(root, App):
            return App(eval_t(root.f), eval_t(root.arg))

        if isinstance(root, Arrow):
            return Arrow(eval_t(root.arg), eval_t(root.ret))

        if isinstance(root, Tuple):
            return Tuple(tuple(map(eval_t, root.elts)))

        if isinstance(root, Implicit):
            return Implicit(eval_t(root.witness), eval_t(root.type))
        if isinstance(root, Forall):
            return Forall(root.scope, root.fresh_vars, root.poly_type)
        if isinstance(root, Record):
            return Record(eval_row(root.row))
        raise TypeError(root)

    return visit_t


def visit_check(f: t.Callable[[T], bool]):
    def eval_t(root: T) -> bool:
        if not f(root):
            return False

        def eval_row(root) -> bool:

            if isinstance(root, RowCons):
                return eval_t(root.field_type) and eval_row(root.tail)
            if isinstance(root, RowMono):
                return True
            if isinstance(root, RowPoly):
                return eval_t(root.type)
            raise TypeError(root)

        if isinstance(root, LeafTypes):
            return True
        if isinstance(root, App):
            return eval_t(root.f) and eval_t(root.arg)
        if isinstance(root, Arrow):
            return eval_t(root.arg) and eval_t(root.ret)
        if isinstance(root, Tuple):
            return all(map(eval_t, root.elts))
        if isinstance(root, Implicit):
            return eval_t(root.witness) and eval_t(root.type)
        if isinstance(root, Forall):
            return eval_t(root.poly_type)
        if isinstance(root, Record):
            return eval_row(root.row)
        raise TypeError(root)

    return eval_t


def row_from_list(xs: t.List[t.Tuple[str, T]], last: Row) -> Row:
    for k, v in xs:
        last = RowCons(k, v, last)
    return last


def row_of_map(d: t.Dict[str, T], last: Row) -> Row:
    for k, v in d.items():
        last = RowCons(k, v, last)
    return last


def normalize_forall(forall_scope: ForallGroup, bounds: t.Iterable[str], poly):
    bounds = set(bounds)
    maps = {}

    def _visit_func(_, ty):
        if isinstance(ty, UnboundFresh):
            s = ty.n
            f_var = maps.get(s, None)
            if f_var is None:
                f_var = maps[s] = Fresh(s, forall_scope)
            return (), f_var

        return (), ty

    poly = pre_visit(_visit_func)(poly)
    left = bounds ^ maps.keys()
    if left:
        warn(UserWarning("Redundant free variables {}".format(left)))

    return Forall(forall_scope, tuple(maps.values()), poly)


class OnceTypeMismatch(Exception):
    pass
