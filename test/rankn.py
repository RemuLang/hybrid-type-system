from hybridts.tc_state import TCState
from hybridts import type_encoding as te
import sys

sys.setrecursionlimit(100)
tctx = {}

tcs = TCState(tctx)

# forall1 = te.forall_t, frozenset(["a"]), (te.arrow_t, (te.fresh_t, "a"),
#                                           (te.forall_t, frozenset(["b"]), (
#                                               te.arrow_t,
#                                               (te.fresh_t, "b"),
#                                               (te.fresh_t, "b"),
#                                           )))
#
# int_t = tcs.mk_new_type("base.int")
# arg = int_t
# ret = tcs.new_var()
#
# arrow = te.arrow_t, arg, ret
# tcs.unify(arrow, tcs.inst(forall1))
# print(tcs.infer(arg))
# print(tcs.infer(ret))
#
#
# x = tcs.new_var()
# f = mk_forall({"a"}, mk_arrow(mk_fresh("a"), mk_fresh("a")))
# k = mk_arrow(
#     mk_forall({"a"}, mk_fresh("a")),
#     int_t
# )
#
# tcs.unify(mk_arrow(tcs.inst(f), x), k)
#
# print(tcs.infer(x))

sun = te.InternalVar(is_rigid=False)
# forall a. a -> a

mk_fresh = lambda x: te.UnboundFresh(x)
bot = te.normalize_forall(['a'], mk_fresh("a"))


def mk_forall(xs, t: te.T, name=None):
    return te.normalize_forall(xs, t)


mk_arrow = lambda x, y: te.Arrow(x, y)

# forall a. a -> a
# auto = mk_forall({"a"}, mk_arrow(mk_fresh("a"), mk_fresh("a")))
#
# # forall a. a -> a -> a
# choose = mk_forall({"a"}, mk_arrow(mk_fresh("a"), mk_arrow(mk_fresh("a"), mk_fresh("a"))))
# choose2 = mk_arrow(bot, mk_arrow(bot, bot))
# tcs.unify(mk_arrow(auto, x), tcs.inst(choose))
# print(tcs.infer(x))

# f: forall a. a -> a
# g: (int -> int) -> int
# g f

# skip


class Var(te.Var):
    def __init__(self, name):
        self.is_rigid = False
        self.topo_maintainers = set()
        self.name = name

    def __repr__(self):
        return self.name


int_t = te.InternalNom("int")

sun = Var("sun")
f = mk_forall(["x"], mk_arrow(mk_fresh('x'), sun))
# print(tcs.infer(f))

sam = Var("sam")
zak = Var("zak")
_, f_ = tcs.inst_with_structure_preserved(f)
tcs.unify(f_, mk_arrow(sam, zak))

tcs.unify(zak, sam)

print(tcs.infer(f_))
print(tcs.infer(f))

print('===')
deps = tcs.get_structures()

# for ftv in te.ftv(f_):
#     print(deps.get(ftv))
