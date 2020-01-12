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

arg : forall a. a -> a
f   : (int -> int) -> int

"""