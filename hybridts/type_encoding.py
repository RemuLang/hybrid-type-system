import abc
import typing as t
from hybridts import exc
from warnings import warn
from dataclasses import dataclass

DEBUG = True


class Fresh:
    name: str
    token: 'token'

    def __init__(self, name: str, token: object):
        self.name = name
        self.token = token

    def __repr__(self):
        return self.name


class ForallGroup:
    pass


class InternalForallScope(ForallGroup):
    def __init__(self, name: str):
        self._name = name

    def __repr__(self):
        return '{}'.format(self._name)


class Var:
    is_rigid: bool


_encode_list = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!@#$%^&*()_+{}[]|\\:;" '<,>.?/'
_base = len(_encode_list)


def _shorter_string_base(num):
    res = []
    app = res.append
    while num != 0:
        app(_encode_list[num % _base])
        num //= _base
    return ''.join(res)


if DEBUG:
    cnt = 0

    class InternalVar(Var):
        """
        This kind of type variable is not user-created, but you does can,
        if you don't mind the bad error reporting :)
        """
        is_rigid: bool

        def __init__(self, is_rigid: bool):
            global cnt
            self.is_rigid = is_rigid
            self.id = cnt
            cnt += 1

        def __repr__(self):
            return '<{} var|{}>'.format(
                'rigid' if self.is_rigid else 'flexible', self.id)

else:

    class InternalVar(Var):
        """
        This kind of type variable is not user-created, but you does can,
        if you don't mind the bad error reporting :)
        """
        is_rigid: bool

        def __init__(self, is_rigid: bool):
            self.is_rigid = is_rigid

        def __repr__(self):
            return '<{} var|{}>'.format(
                'rigid' if self.is_rigid else 'flexible',
                _shorter_string_base(id(self)))


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

    def __repr__(self):
        if isinstance(self.arg, SimplyReprType):
            return '{!r} {!r}'.format(self.f, self.arg)
        return '{!r} ({!r})'.format(self.f, self.arg)


@dataclass(eq=True, frozen=True, order=True)
class Arrow:
    arg: 'T'
    ret: 'T'

    def __repr__(self):
        if isinstance(self.arg, SimplyReprType):
            return '{!r} -> {!r}'.format(self.arg, self.ret)
        return '({!r}) -> {!r}'.format(self.arg, self.ret)


class Nom(abc.ABC):
    @abc.abstractmethod
    def get_name(self) -> str:
        raise NotImplementedError

    def __repr__(self):
        return self.get_name()


class InternalNom(Nom):
    def __init__(self, name):
        self._name = name

    def get_name(self) -> str:
        return self._name


def _repr_many(xs):
    return map(repr, xs)


@dataclass(eq=True, frozen=True, order=True)
class Tuple:
    elts: t.Tuple['T', ...]

    def __repr__(self):
        return '({})'.format(', '.join(_repr_many(self.elts)))


class Forall:
    token: object
    fresh_vars: t.Tuple[Fresh, ...]
    poly_type: 'T'

    def __init__(self, token: object, fresh_vars: t.Tuple[Fresh, ...], poly_type: 'T'):
        self.token = token
        self.fresh_vars = fresh_vars
        self.poly_type = poly_type

    def __repr__(self):
        return 'forall {}. {!r}'.format(' '.join(_repr_many(self.fresh_vars)),
                                        self.poly_type)


@dataclass(eq=True, frozen=True, order=True)
class Record:
    row: Row

    def __repr__(self):
        fields, tho = extract_row(self.row)
        field_str = ', '.join('{}: {!r}'.format(k, t)
                              for k, t in fields.items())
        if not tho:
            return '{{{}}}'.format(field_str)
        return '{{{}|{!r}}}'.format(field_str, tho)


@dataclass(eq=True, frozen=True, order=True)
class Implicit:
    witness: 'T'
    type: 'T'


@dataclass(eq=True, frozen=True, order=True)
class UnboundFresh:
    n: str


T = t.Union[App, Arrow, Var, Nom, Fresh, Tuple, Forall, Record, Implicit,
            UnboundFresh]
Path = t.Union[App, Arrow, Var, Fresh, Tuple, Forall, Record, Implicit]
TypeCtx = t.Dict[Var, t.Tuple[t.Optional[Path], T]]
Handler = t.Callable

SimplyReprType = (Var, Nom, Fresh, Tuple, Record)

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
            return Forall(root.token, root.fresh_vars, eval_t(root.poly_type))

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


def normalize_forall(bounds: t.Iterable[str], poly):
    bounds = set(bounds)
    maps = {}
    token = object()

    def _visit_func(_, ty):
        if isinstance(ty, UnboundFresh):
            s = ty.n
            f_var = maps.get(s, None)
            if f_var is None:
                f_var = maps[s] = Fresh(s, token)
            return (), f_var

        return (), ty

    poly = pre_visit(_visit_func)((), poly)
    left = bounds ^ maps.keys()
    if left:
        warn(UserWarning("Redundant free variables {}".format(left)))

    return Forall(token, tuple(maps.values()), poly)


def ftv(t):
    vars: t.Set[Var] = set()

    def _visit(t):
        if isinstance(t, Var):
            vars.add(t)
        return True

    visit_check(_visit)(t)
    return vars


def _variable_fresh_visitor(mapping: dict, t: 'T') -> t.Tuple[dict, 'T']:
    v = mapping.get(t)
    if v:
        return mapping, v
    if isinstance(t, Var):
        v = mapping[t] = InternalVar(is_rigid=False)
        return mapping, v
    return mapping, t


_fresh_vars = pre_visit(_variable_fresh_visitor)


def fresh_vars(t: T, mapping=None) -> T:
    if mapping is None:
        mapping = {}
    return _fresh_vars(mapping, t)


_var_and_fresh = (Var, Fresh)


def _variable_and_bound_fresh_visitor(mapping: dict, t: 'T') -> t.Tuple[dict, 'T']:
    v = mapping.get(t)
    if v:
        return mapping, v
    if isinstance(t, _var_and_fresh):
        v = mapping[t] = InternalVar(is_rigid=False)
        return mapping, v
    return mapping, t


_fresh_vars_and_bounds = pre_visit(_variable_and_bound_fresh_visitor)


def fresh_vars_and_bounds(t: T, mapping=None) -> T:
    if mapping is None:
        mapping = {}
    return _fresh_vars_and_bounds(mapping, t)


def _bound_but_no_var_fresh_visitor(mapping: dict, t: 'T') -> t.Tuple[dict, 'T']:
    v = mapping.get(t)
    if v:
        return mapping, v
    if isinstance(t, Fresh):
        v = mapping[t] = InternalVar(is_rigid=False)
        return mapping, v
    if isinstance(t, Var):
        raise exc.ShouldntFreshVarHere
    return mapping, t


_fresh_bound_but_no_var = pre_visit(_variable_and_bound_fresh_visitor)


def fresh_bound_but_no_var(t: T, mapping=None) -> T:
    if mapping is None:
        mapping = {}
    return _fresh_bound_but_no_var(mapping, t)


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
