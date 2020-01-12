from hybridts.tc_state import TCState
from hybridts import type_encoding as te

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

x = te.InternalVar(is_rigid=False)
# forall a. a -> a

mk_fresh = lambda x: te.UnboundFresh(x)
bot = te.normalize_forall(te.InternalForallScope("bot"), ['a'], mk_fresh("a"))

cnt = 0
def mk_forall(xs, t: te.T, name=None):
    global cnt
    if not name:
        cnt += 1
        name = str(cnt)
    return te.normalize_forall(te.InternalForallScope(name), xs, t)


mk_arrow = lambda x, y: te.Arrow(x, y)

# forall a. a -> a
auto = mk_forall({"a"}, mk_arrow(mk_fresh("a"), mk_fresh("a")))

# forall a. a -> a -> a
choose = mk_forall({"a"}, mk_arrow(mk_fresh("a"), mk_arrow(mk_fresh("a"), mk_fresh("a"))))
choose2 = mk_arrow(bot, mk_arrow(bot, bot))
tcs.unify(mk_arrow(auto, x), tcs.inst(choose))
print(tcs.infer(x))

# forall a. a -> a
# (int -> int) -> int



# y = te.InternalVar(is_rigid=False)
# tcs.unify(mk_arrow(tcs.inst(auto), y), tcs.inst(choose2))
#
# print(tcs.infer(y))
