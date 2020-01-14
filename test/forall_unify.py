from hybridts.tc_state import TCState
from hybridts.tc_make import RigidStructureKeeper
from hybridts import type_encoding as te

cnt = 0
tcs = TCState({})

list = te.InternalNom("list")
var = te.InternalVar(is_rigid=False)

t1 = te.normalize_forall(["x"], te.App(list, te.UnboundFresh("x")))
t2 = te.normalize_forall(["x"], te.App(var, te.UnboundFresh("x")))

tcs.unify(t1, t2)
print(tcs.infer(var))
for _, v in tcs.get_structures().items():
    for r in v:
        if isinstance(r, RigidStructureKeeper):
            print('+++')
            print(tcs.infer(r.template))
            print(tcs.infer(r.path))


