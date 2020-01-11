from hybridts.tc_state import TCState
from hybridts.type_encoding import row_of_map, record_of_row, poly_row, empty_row
from hybridts import type_encoding as te

tctx = {}

tcs = TCState(tctx)

forall1 = te.forall_t, frozenset(["a"]), (te.arrow_t, (te.fresh_t, "a"),
                                          (te.forall_t, frozenset(["b"]), (
                                              te.arrow_t,
                                              (te.fresh_t, "b"),
                                              (te.fresh_t, "b"),
                                          )))

int_t = tcs.mk_new_type("base.int")
arg = int_t
ret = tcs.new_var()

arrow = te.arrow_t, arg, ret
tcs.unify(arrow, tcs.inst(forall1))
print(tcs.infer(arg))
print(tcs.infer(ret))

x1 = tcs.new_var()
x2 = tcs.new_var()
arrow = te.arrow_t, x1, (te.arrow_t, x2, int_t)
tcs.unify(arrow, tcs.inst(forall1))
print(tcs.infer(x1))
print(tcs.infer(x2))
print(tcs.infer(arrow))

