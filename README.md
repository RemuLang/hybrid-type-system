# The Hybrid Type System

Row + Implicit arguments + MLF(WIP).  

## Notes about System F

Before implementing MLF:
```
choose: forall a. a -> a -> a
auto  : forall a. a -> a
(choose auto) : (forall a. a —> a) -> (forall a. a -> a)


// if auto is defined without annotations, polymorphisms of lambdas get lost
auto2 : a -> a
(choose auto) : (a -> a) -> (a -> a)  
```  

## Notes about System F-Omega

Kind checker is not implemented. 

## Usage

```python
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
print(tcs.infer(r1)) # {b: base.int, a: base.int}
print(tcs.infer(r2)) # {a: base.int, b: base.int}



int_t = te.InternalNom("int")

class Var(te.Var):
    is_rigid = False
    def __init__(self, name):
        self.name = name
    __repr__ = lambda self: self.name


ret = Var("ret")
# f: forall x. x -> ?ret
f = te.normalize_forall(te.InternalForallScope(""), ["x"],
                        te.Arrow(te.UnboundFresh('x'), ret))

sam = Var("sam")
zak = Var("zak")

# typeof(f_) = instantiate typeof(f)
# f_: x' -> ?ret'
f_ = tcs.inst(f)

# x' -> ?ret' = sam -> zak
tcs.unify(f_, te.Arrow(sam, zak))
# zak = sam
tcs.unify(zak, sam)

print(tcs.infer(f_)) # sam -> sam
print(tcs.infer(f)) # forall x. x -> x
print(tcs.infer(zak)) # sam
```