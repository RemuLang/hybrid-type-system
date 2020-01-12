from hybridts.tc_state import TCState
from hybridts.type_encoding import row_of_map, record_of_row, poly_row, empty_row
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
# f = te.mk_forall({"a"}, te.mk_arrow(te.mk_fresh("a"), te.mk_fresh("a")))
# k = te.mk_arrow(
#     te.mk_forall({"a"}, te.mk_fresh("a")),
#     int_t
# )
#
# tcs.unify(te.mk_arrow(tcs.inst(f), x), k)
#
# print(tcs.infer(x))

x = tcs.new_var()
# forall a. a -> a
auto = te.mk_forall({"a"}, te.mk_arrow(te.mk_fresh("a"), te.mk_fresh("a")))
# forall a. a -> a -> a
choose = te.mk_forall({"a"}, te.mk_arrow(te.mk_fresh("a"), te.mk_arrow(te.mk_fresh("a"), te.mk_fresh("a"))))

choose2 = te.mk_arrow(te.bot, te.mk_arrow(te.bot, te.bot))

tcs.unify(te.mk_arrow(tcs.inst(auto), x), tcs.inst(choose))

print(tcs.infer(x))

y = tcs.new_var()
tcs.unify(te.mk_arrow(tcs.inst(auto), y), tcs.inst(choose2))

print(tcs.infer(y))

"""
a -> b -> b
b -> a

a -> a
(b -> b) -> b
(a, b -> b)
fail

a allocated by side1
b allocated by side2
(b, a) -> normalized -> (a, b)

once type is temporary nominal type! 
a = (b -> b)
a -> a = b
how fail?

subst other side's once vars with its own side's once vars,
    if cannot(not principal), fail
    otherwise, resume type mapping from once types to (fresh types and slot types),
        use infer to prune.     
    
    Note that slot types can reach external scope.
    !!!so fresh should fail, when unifying!!!
    !!!checking forall, always making once types!!!
    
    Another side?
    
    arg : forall a . a -> a
    f: ( int -> int ) -> int
    f arg
    once types become nominal types, so just ignore the substitution.
    
    but we should return a type for representation the instantiated type:
    arg_inst : int -> int, {a : int}
    
    so do not make once vars only alive during one `unify`!!
    
    we make a "onced" type from each HS before unifying, which returns 2 maps.
    each map is from (fresh + var) to once.
    
    after unifying, we the maps are updated. 
    
    var   -> once, and once = fresh  => don't update
                       once != fresh, substitute
    fresh -> once, and once = fresh  => update 
    

unify end, once vars get out of dated, if found use again, failed.

f : forall a. ?var
g : forall b. b

Kf : {var: v1}
Kg : {b: v2}
f' = g' is v1 = v2
[v1 = v2]

for f: [var = v2], okay
for g: [v1  = b], okay 

??

arg : forall a . a -> a
f: ( int -> int ) -> int
f arg
Karg : {a : v}
Kf   : {}

[a = int -> int]
a = int => int -> int = int failed

arg : forall a . a -> a
f: ( forall b. b -> b ) -> var
Karg : {a : v1}
Kf   : {b : v2, var: v3}

[v1 = v2, v1 = v3]

for f: [v1 = b, v1 = var], okay, but var assign to b, we should then check the scope of (forall b)!
for arg: [a = v2], okay

how to get inst of arg?, arg_inst [a -> a][a = v2] = v2 -> v2, however, no one will use v2,
so after tc, v2 is a top level forall vars!

forall v2.
    program 
?? program allows outer resolution?
   program allows only current module resolution.
   by what keyword? 
    module Mine with forall
    module Main
    great design!
    
    (module A with forall
        let x = fun x -> x) : forall a. {x : a}

auto: forall a. a -> a
choose: forall a. a -> a -> a



f: (forall a. a -> a) -> int
arg : int -> int
?? f arg should fail
!! don't inst automatically!

(arg of f) >= arg 

f: (forall a. a -> a) -> int
arg : (forall b. [b] -> [b])
?? f arg? should fail
f : {a: v1}
arg: {b: v2}
v1 = [v2]

so, fresh var `a` in f is like nominal type, shouldn't expand.
    fresh var `v` in arg is like var type, can expand.

tcs.rigid_inst(f) unify (tcs.flexible_inst(arg) -> var), nice 

besides, when unifying, forall can only do rigid instance.

user can manually flexibly expand types, such as argument type!

nice!

So, now, the problem gets raised: how should we implement rigid once type and flexible once type?
1. checking scope exceeding problem after unifying
2. assign a kind to once to indicate it is rigid or flexible?
    if rigid, okay for assigned to a type var
              okay for making once equality to another once type
              fail for other cases
    if flexible,
              okay to perform like a normal type var

So flexible once type is only a normal type var?
Why once type? To guarantee any checking with once type fail after leaving the given forall scope.

f : forall a. a -> var
arg : a' -> a', (a' is a type var)

 
Kf: {a: v1, var: v3}, v1 is rigid
Karg: {a': v2}, v2 is flexible
v1, v2, v3 is closed in this scope

[v1 = v2, v3 = v2]

for arg: {a' : v1'=infer(v1)},
    a' is tvar, unify a' v1'
for f:
    a is fresh,  {a: v2, var: v2}

f: forall a. a -> var
g : a' -> b'
f unify g

Kf : {a: v1, var: v2}
Kg : {a': v3, b': v4}

    !!! v1, v2, v3, v4 is closed! 
[v1 = v3, v2 = v4] (Efg  -------------------------------------------------------------------
                                                                                           |
g unify h                                                                                  |
h : z' -> z'                                                                               |
Kg : {a': v5, b': v6}                                                                      |
Kh: {z': v7}
[v5 = v7, v6 = v7]

for g: {a': v7, b' = v7}

infer(f) trigger Kf pruning                                                                 |
    {v7: v3, v7: v4}                                                                        |
    [v1 = v3, v2 = v4] -> [v7 = v3 = v4 = v1 = v2]                                          |
    {a: v1, var: v2} -> {a: v7, var: v7}, var = a                                           |
                                                                                            |
Hence, we have to keep the Klhs and Krhs and (unification or K values)                      |
                                                                                            | 
 any change to one of {var, 'a, 'b} will trigger the update of ------------------------------
    Kf, Kg and Efg
    
    Map from a type variable to its related relations:
        key = var
        value = infer(var), [(Kf, Kg, Efg)]
    So, when var chanegd, mark if the relation map is "dirty",
    we will update all "dirty" ones.
 
    class LocalTypeTopology:
        Klhs      : [(T, T)] # the left is from outer universe, the right is from LocalTypeTopology's university
        Krhs      : [(T, T)] 
         
        maintainer : TCState # the LocalTypeTopology's universe
        
        # if every type var is `maintainer` has a reference, we called this topo "solved" 
        if solved, we should delete this local type topology:
        we delete reference of current topo from [each[0].topo_maintainers for each in Klhs]
                                             and [each[0].topo_maintainers for each in Krhs]
        
        
can outer type var get used by inner universe directly?
f1 : forall a. a -> var
f2 : a' -> 'b


blablabla, 

when auto unifying:
    forall a. a -> a
    forall b. b -> b
    both sides turn out to be rigid.
    but, to make this fail:
        forall a. a -> a
        forall b. b -> int
    only rigid is not enough,
    we try to assign one rigid initially.
    
    f: forall a. a -> a
    g: forall b. b -> var
    
    Kf: {a: v1}
    Kg: {b: v2, var: var'}
    [v1 = v2, v1 = var']
    Kf: {a: v2}
    Kg: {b: v2}
    
    
    so, finally(after the inner universe ended),
    for K {a: int, b: int}, we judge it as type check failure according to
     "fresh variable can and can only bidirectionally equal to another fresh variable in another side."
        
        
        
    

"""