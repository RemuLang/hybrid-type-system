from hybridts.tc_state import TCState
from hybridts import type_encoding as te
tctx = {}

tcs = TCState(tctx)

x1 = te.InternalVar(is_rigid=False)
x2 = te.InternalVar(is_rigid=False)

int_t = te.InternalNom("base.int")

tcs.unify(x1, int_t)
tcs.unify(x1, x2)


assert tcs.infer(x1) == int_t
assert tcs.infer(x2) == int_t

x3 = te.InternalVar(is_rigid=False)

r1 = te.row_of_map({'a': x1, 'b': x3}, te.empty_row)
r1 = te.Record(r1)
tho = te.InternalVar(is_rigid=False)
r2 = te.row_of_map({'a': x3}, te.RowPoly(tho))
r2 = te.Record(r2)
tcs.unify(r1, r2)
print(tcs.infer(r1))
print(tcs.infer(r2))







