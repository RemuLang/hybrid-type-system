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

## Restrictions

- Temporary restrictions: cannot automatically compute principal types, so first class polys need annotations.
- Higher Order Unification: `TCState.inst_without_structure_preserved` only works when
    - Any cases of unifying 2 poly types
    - A poly type contains free type variables, to unify it with a monotype, this poly type can only hold one bound variables.
    - Unifying a monotype with, a poly type without free type variables.
   
Don't do this:
```shell script
TCState.inst_without_structure_preserved(forall a b. a -> 'ftv) unify (a -> a)
```

P.S: Currently, `(forall a. a -> var) unify ((i -> j) -> (j -> i))` won't lead to failure, this is in the TO-DO list.
Actually, only when `i` and `j` are inferred to point to another non-variable type should above unification fail. 
 
      
## Usage

```python
from hybridts import type_encoding as te
from hybridts.tc_state import TCState

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
f = te.normalize_forall(["x"], te.Arrow(te.UnboundFresh('x'), ret))

sam = Var("sam")
zak = Var("zak")

# typeof(f_) = instantiate typeof(f)
# f_: x' -> ?ret'
_, f_ = tcs.inst_with_structure_preserved(f)
# x' -> ?ret' = sam -> zak
tcs.unify(f_, te.Arrow(sam, zak))
# zak = sam
tcs.unify(zak, sam)

print(tcs.infer(f_)) # sam -> sam
print(tcs.infer(f)) # forall x. x -> x
print(tcs.infer(zak)) # sam

ret = Var("ret")
# f: forall x. x -> ?ret
f = te.normalize_forall(["x", "y"],
                        te.Arrow(
                            te.UnboundFresh('x'),
                            te.Tuple(
                                (te.UnboundFresh("x"), te.UnboundFresh("y")))))

sam = Var("sam")
zak = Var("zak")

# typeof(f_) = instantiate typeof(f)
# f_: x' -> ?ret'
_, f_ = tcs.inst_without_structure_preserved(f)

# x' -> ?ret' = sam -> zak
tcs.unify(f_, te.Arrow(sam, te.Tuple((sam, sam))))
# zak = sam
# tcs.unify(zak, sam)

print(tcs.infer(f_)) # sam -> (sam, sam)
print(tcs.infer(f)) # forall x y. x -> (x, y)
# print(tcs.infer(zak))
```