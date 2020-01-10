from mlftt.tc_state import TCState
from mlftt.type_encoding import record_of_map, record_of_row, poly_row, empty_row

tctx = {}

tcs = TCState(tctx)

x1 = tcs.new_var()
x2 = tcs.new_var()

int_t = tcs.mk_new_type("base.int")
tcs.unify(x1, int_t)
tcs.unify(x1, x2)


assert tcs.infer(x1) == int_t
assert tcs.infer(x2) == int_t

x3 = tcs.new_var()

r1 = record_of_map({'a': x1, 'b': x3}, empty_row)
r1 = record_of_row(r1)
tho = tcs.new_var()
r2 = record_of_map({'a': x3}, poly_row(tho))
r2 = record_of_row(r2)
tcs.unify(r1, r2)
print(tcs.infer(r1))
print(tcs.infer(r2))







