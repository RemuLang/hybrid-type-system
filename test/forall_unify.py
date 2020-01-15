from hybridts.tc_state import TCState

from hybridts import type_encoding as te

cnt = 0
tcs = TCState({})

list = te.InternalNom("list")
var = te.InternalVar(is_rigid=False)

t1 = te.normalize_forall(["x"], te.App(te.UnboundFresh("x"), te.UnboundFresh("x")))
t2 = te.normalize_forall(["x"], te.App(var, te.UnboundFresh("x")))

tcs.unify(t1, t2)
print(tcs.infer(var))


