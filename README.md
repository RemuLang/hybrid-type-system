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
from hybridts.type_encoding import row_of_map, record_of_row, poly_row, empty_row

tctx = {}

tcs = TCState(tctx)

x1 = tcs.new_var()
x2 = tcs.new_var()

int_t = tcs.mk_new_type("base.int") # nominal type
tcs.unify(x1, int_t)
tcs.unify(x1, x2)


assert tcs.path_infer(x1) == int_t
assert tcs.path_infer(x2) == int_t

x3 = tcs.new_var()

r1 = row_of_map({'a': x1, 'b': x3}, empty_row)
r1 = record_of_row(r1)
tho = tcs.new_var()
r2 = row_of_map({'a': x3}, poly_row(tho))
r2 = record_of_row(r2)
tcs.unify(r1, r2)
print(tcs.path_infer(r1))
print(tcs.path_infer(r2))

# (RecordT, (RowConsT, 'b', (NomT, 'base.int'), (RowConsT, 'a', (NomT, 'base.int'), (RowMonoT,))))
# (RecordT, (RowConsT, 'a', (NomT, 'base.int'), (RowPolyT, (RecordT, (RowConsT, 'b', (NomT, 'base.int'), (RowMonoT,)
```