require import Int FinType Real.
   
qmodule type Foo_t = {
  qproc a(x:int) : int
}.
(*realize typing_0. auto. qed.
realize typing_1. auto. qed.*)

qmodule type Foo2_t = {
  qproc c(x:int) : int
}.
(*realize typing_0. auto. qed.
realize typing_1. auto. qed.*)
     
module Foo : Foo_t = {
  var ctr: int
  var f: int -> int
  
  qproc a(x) = { 
    ctr <- ctr + 1; 
    return f x; }

    (* Virtual proc:
     proc a_true{x,y} = { ctr += 1; Uc[f] on x,y } 
     (accessible to adv)
     *)
            
(*  quantum proc b{x} = { 
    quantum var y; 
    y <@ a{x}; 
    y <@ a{y}; 
    return y; 
    }
*)

    (* b/c ----> proc{x,y} = { ctr += 2; Uc[f^2] on x,y } *)

    (* "Right" virtual proc:
       
       proc b_true{x,y}:
       
       quantum var z <- |0>;
       a_true{x,z}
       a_true{z,y}
       a_true{x,z}
             
    
      == { ctr +=3 ; Uc[f^2] }
      
      Works easiest if:
      - Allow classical side effect in quantum procs.
      - Do not allow f to depend on side-effected variables (incl. side-effected variables in
      recursively invokes quantum-procs)
      
           (Could still be valid, but we will not be allowed to use equiv-reasoning compositionally on them)
      
    *)
        
  }.

(*realize typing_0. auto. qed.
realize typing_1. auto. qed.*)

module Foo2 : Foo2_t = {

  qproc c(x) = {
    Foo.ctr <- Foo.ctr + 2;
    return Foo.f (Foo.f x);
  }   
}.
(*
realize typing_0. auto. qed.
realize typing_1. auto. qed.*)

  
type T.

qmodule type A_t(F: Foo_t) = {
  proc run() : T
}.

qmodule type A2_t(F2: Foo2_t) = {
  proc run() : T
}.

(* A saitsfying result can be found by computing Uc[f^2] on uniform superpos. *)
op test : (int -> int) -> T -> bool.

(*
module Evil_A(Foo2:Foo2_t) = {
  proc run(): T = {
    (* ... create equal superposition ...
    ... run Foo2.c on it ...
    ... do some measurement ...
    ... return result ... *)
    return witness;
  }
}.*)


module Game2(A2:A2_t) = {
  proc main() : bool = {
    var result : T;
    Foo.f <$ witness;
    Foo.ctr <- 0;
    result <@ A2(Foo2).run();
    return test Foo.f result /\ Foo.ctr <= 2;
  }
}.


module Game(A:A_t) = {
  proc main() : bool = {
    var result : T;
    Foo.f <$ witness;
    Foo.ctr <- 0;
    result <@ A(Foo).run();
    return test Foo.f result /\ Foo.ctr <= 2;
  }
}.

(* Claim *)
lemma claim1 &m: exists (Evil_A2 <: A2_t{-Foo,-Foo2}), Pr[Game2(Evil_A2).main() @ &m : res] = 1%r.
admit.
qed.

lemma claim2 &m: forall (Evil_A <: A_t{-Foo,-Foo2}), Pr[Game(Evil_A).main() @ &m : res] < 1%r.
admit.
qed.

(*
Only way to compute Uc[f^2] using quantum circuit is:

Registers X,Y

Aux register Z <- |0>

goodf2:
X,Z <- Uc[f]
Z,Y <- Uc[f]
X,Z <- Uc[f] // Z is back to |0>

badf2:
X,Z <- Uc[f]
Z,Y <- Uc[f]


X <- |+>
Y <- |0>
badf2
badf2

|00> + |10>
|0 0 f0> + |1 0 f1>
|0 ff0 f0> + |1 ff1 f1>
|0 ff0 f0 f0> + |1 ff1 f1 f1>
|0 0 f0 f0> + |1 0 f1 f1>
Measure: X in diagonal basis --> Prob = 1/2


Uc[f^2]-twice on XY == id on XY
Say X = |+>    Y = |0>
Should get |+> |0>
Do get:  



*)


module Evil_2(A2: A2_t)(Foo: Foo_t) = {
  module MyFoo2 : Foo2_t = {
          
  qproc c(x) = { 
    var y; 
    y <@ Foo.a(x); 
    y <@ Foo.a(y); 
    return y; 
    }
  }
    
  proc run() = {
    var result : T;
    result <@ A2(MyFoo2).run();
    return result;    
  }
}.

(*realize typing_0. auto. qed.
realize typing_1. auto. qed.*)


(* Evil_2(A2)(Foo) == A2(Foo2) *)

section.

declare qmodule A2 <: A2_t{-Foo, -Foo2}.

equiv toto: Evil_2(A2, Foo).run ~ A2(Foo2).run : ={glob A2} /\ ={glob Foo} 
 ==> ={res}.
 (* Needs to be changed and given clear semantics. *)
 
 
 proc * .
 inline *.
 wp.
 call (_: ={glob Foo}). 
  (* Potentially unsound: read in two meaning:
  
  - an equiv of Evil_2....c_true ~ Foo2.c_true  (A)
  - an equiv of Evil_2....c ~ Foo2.c in some kind-of classical way  (B)
  
  call is sound with meaning (A)
  
   *)
  
proc.   (* Uses meaning (B).
Need for soundness:

(B)  implies  (A)


 *)
inline *.
wp.
skip.
auto.
skip.
auto.
qed.
 

lemma test2 &m: Pr[Game(Evil_2(A2)).main() @ &m : res] = Pr[Game2(A2).main() @ &m : res].
byequiv.
proc*.
inline*.
wp.

 
 
lemma test &m: Pr[Game(Evil_2(A2)).main() @ &m : res] = 1%r.
  elim (claim1 &m).

  
  
  (*
  
    quantum proc also_tricky{x} = { 
    quantum var y; 
    y <@ Foo.a{x}; 
    return g y; 
    }
  }

  
  *)

  
  
  
  (*
  
  
  Stuff in pre/postconditions:
  
  - classical stuff
  - =Q  (in EasyPQC paper, also in tool?)
  
  - New: x \in expr   (x quantum var)
  
  
  
  *)
