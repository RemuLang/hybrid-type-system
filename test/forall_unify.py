from hybridts.tc_state import TCState
from hybridts import type_encoding as te

cnt = 0
tcs = TCState({})
class Var(te.Var):
    def __init__(self, name):
        self.is_rigid = False
        self.topo_maintainers = set()
        self.name = name
    def __repr__(self):
        return self.name


def mk_forall(xs, t: te.T, name=None):
    global cnt
    if not name:
        cnt += 1
        name = str(cnt)
    return te.normalize_forall(te.InternalForallScope(name), xs, t)

hola = Var("hola")

t1 = mk_forall(["a"], te.Arrow(te.UnboundFresh("a"), hola))

ppt = Var("ppt")
mid = Var("mid")

t2 = te.Arrow(t1, t1)

tcs.unify(tcs.inst(t1), mid)
tcs.unify(tcs.inst(t1), t2)
print(tcs.infer(t1))