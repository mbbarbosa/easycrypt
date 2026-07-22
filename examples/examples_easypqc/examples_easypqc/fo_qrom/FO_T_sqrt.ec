require import AllCore RealExp Distr DBool List FinType. 
require (****) T_OW2H.

type msg.
type pkey.
type cph.
type rand.

(**************************************************************)
(*                                                            *)
(*                   PKE Definitions                          *)
(*                                                            *)
(**************************************************************)

op enc : pkey -> msg -> rand -> cph.

op [lossless]kgen : pkey distr.

clone import MUniFinFun with
   type t <- msg.

clone import FinType as FinRand with
   type t <- rand.

op [lossless]md : msg distr.
op [lossless]rd : rand distr.
op [lossless]hd = dfun (fun _ => rd).

axiom md_funi : is_funiform md.

module type RO_t = {
   quantum proc o{x : msg} : rand
   proc oC(x : msg) : rand
}.

module RO : RO_t = {
   var h : msg -> rand
   proc init() = { h <$ hd; }
   quantum proc o{x : msg} : rand = {
      return h x;
   }
   proc oC(x : msg) : rand = {
      return h x;
   }
}.

quantum module type INDADV = {
   proc dist(pk : pkey, m0 m1 : msg, c : cph) : bool
}.

module INDKPA(A : INDADV) = {
   var b : bool
   proc main() : bool = {
      var pk, m0, m1, mb, c, b', r;
      pk <$ kgen;
      m0 <$ md;
      m1 <$ md;
      b <$ {0,1};
      mb <- if b then m1 else m0;
      r <$ rd;
      c <- enc pk mb r;
      b' <@ A.dist(pk, m0,m1,c);
      return b = b';
   }
}.

quantum module type OWAdv(O : RO_t) = {
   proc find(pk : pkey, c : cph) : msg
}.

module OW(A : OWAdv)  = {
   proc main() = {
      var pk, m, c, m',r;
      RO.init();
      pk <$ kgen;
      m <$ md;
      r <@ RO.o{m}; 
      c <- enc pk m r;
      m' <@ A(RO).find(pk,c);
      return m = m';
   }
}.

(**************************************************************)
(*                                                            *)
(*                   Security Proof                           *)
(*                                                            *)
(**************************************************************)

(*  We first add another message to the OW game and choose randomly
    which one to challenge the OW adversary. This hop is conservative. *)

module Game1(A : OWAdv)  = {
   var m0, m1, mb, m' : msg
   proc main() = {
      var pk, c, r, b;
      b <$ {0,1};
      RO.init();
      pk <$ kgen;
      m0 <$ md; 
      m1 <$ md;
      mb <- if (b) then m1 else m0;
      r <@ RO.o{mb}; 
      c <- enc pk mb r;
      m' <@ A(RO).find(pk,c);
      return (m' = mb);
   }
}.

section.

declare module A <: OWAdv{-RO, -Game1}.

lemma hop1 &m :
  Pr[ Game1(A).main() @ &m : res  ] = Pr[ OW(A).main() @ &m : res ].
byequiv => //.
proc; seq 1 0 : #pre; 1: by auto.
call(_: ={glob RO}); 1,2: by sim.
wp;inline *;case (b{1}).
+ by wp;rnd;rnd{1};auto=>/> /#.
by wp;rnd{1};auto => /> /#.
qed.

end section.


clone import T_OW2H as OW2H with
  type X <- msg,
  type Y <- rand,
  type Z <- pkey * cph,
  type W <- msg.

import SemiClassicalSQRT.
(* This defines the joint distribution that we will
   use to hop from Game1 to Game2. Note that we
   puncture on two points, m0 and m1. *)
module I : Init = {
  var b : bool
  proc prm() : (msg -> rand) * 
               (msg -> rand) * (msg -> bool) * 
               (pkey * cph) * (msg -> bool) = {
     var pk,c,h,rand0,rand1,sf;
     b <$ {0,1};
     h <$ hd;
     pk <$ kgen;
     Game1.m0 <$ md;
     Game1.m1 <$ md;
     Game1.mb <- if b then Game1.m1 else Game1.m0;         
     c <- enc pk Game1.mb (h Game1.mb);     
     rand0 <$ rd; 
     rand1 <$ rd;
     sf <- fun x => if x = Game1.m0 then rand0 else rand1;
     return (h, sf, 
                fun m' =>m' = Game1.m0 \/ m' = Game1.m1, 
           (pk, c), fun m' => m' = Game1.mb);
  }
}.

(* We take the OW adversary and we transform it into an
   attacker against I. Note the extra call to the
   classical random oracle on m'.  *)
module Awrap(A : OWAdv, O : G_t) = {
   proc run(pk : pkey, c : cph) : msg = {
      Game1.m' <@ A(O).find(pk,c);
      O.oC(Game1.m');
      return Game1.m';
   }
}.

(* We can match the OW2H lemma on the left *)
lemma ow2h_hop_left (A <: OWAdv {-RO, -G, -H, -I, -Game1, -B_O}) &m : 
  Pr [ Game1(A).main() @ &m : res ] =
       Pr [ A_O(Awrap(A),G(I)).main() @ &m : res].
byequiv => //.
proc;inline*;auto => />.
call(_: RO.h{1} = G.g{2}); 1,2: by sim.
auto => />; 1: smt().
by rnd{2};rnd{2}; auto => />.
qed.

(* On the right we are in a game where find always occurs classically
   whenever the adversary causes Ev. This is because the wrapper
   forces this to happen *)
lemma ow2h_hop_right (A <: OWAdv {-RO, -G, -H, -I, -Game1, -B_O}) &m : 
  Pr [ A_O(Awrap(A),H(I)).main() @ &m : res /\ 
              (forall x, G.inS x => ! (x \in G.xs))] = 0%r.
byphoare => //;hoare.
proc;inline*;wp. 
call(_: true); 1,2: by auto. 
by auto => /> /#.
qed.

(* The OW2H bound then gives us this. Note the extra d factor compared
   to the paper, which comes from the fact that we always take the
   explicit B that guesses the query in which A caused find to occur. *)
lemma ow2h_hop (A <: OWAdv {-RO, -G, -H, -I, -Game1, -B_O}) &m d : 
  0 <= d =>
  (forall (O <: RO_t), islossless O.o => islossless O.oC => islossless A(O).find) =>
  (forall (O <: Gi_t), hoare[ A_O(Awrap(A), Count(O)).main : true ==> Count.ch <= d]) =>
  exists (B <: B_t {+Awrap(A)}),
       (forall (O <: G_t) (A0 <: A_t), 
            islossless O.o => 
            islossless O.oC => 
            (forall (O0 <: G_t), islossless O0.o =>   islossless O0.oC => islossless A0(O0).run) =>
            islossless B(O, A0).find) /\
  Pr[ OW(A).main() @ &m : res ] <=
    (2%r * (d%r + 1%r))^2 * Pr[ B_O(H(I),B,Awrap(A)).main() @ &m : res ].
proof. 
move => d_ge0 A_ll A_b.
have [B [#] B_ll BH] := (ow2hsqrt I (Awrap(A)) d &m _ _). 
+ by move => O O_ll OC_ll; islossless; apply (A_ll O O_ll OC_ll). 
+ by apply A_b.
exists B.
split.
+ move =>  O A0 Oll Ocll A0ll. apply (B_ll O A0).
  +  by apply Oll. 
  +  by apply Ocll.
  +  by move => O0 O0ll O0cll;apply (A0ll O0 O0ll O0cll). 
move : BH; rewrite (ow2h_hop_right A &m) sqrt0 /=.
have -> : 2%r * (d%r + 1%r) * sqrt Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res] =
   sqrt ((2%r * (d%r + 1%r))^2 * Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res]).
+ rewrite (sqrtM ((2%r * (d%r + 1%r))^2 ) _). 
  + apply StdOrder.RealOrder.expr_ge0;1: by smt().
    by smt(mu_bounded).
  by rewrite sqrtsq_ge0; smt().
move => HB.
apply sqrt_mono; 1,2: smt(RField.expr2 mu_bounded).
rewrite  -(hop1 A &m)  (ow2h_hop_left A &m).
by smt(RField.expr2).
qed.

(* Now we complete the proof by relating the probability that the
  adversary B works in the SC lemma to the IND-KPA security. The
  reduction is kind of obvious, but the reasoning is not trivial. *)
module Reduction(B : B_t, A : OWAdv) : INDADV  = {
  var nobias : bool
  proc dist(pk : pkey, m0, m1 : msg, c : cph) : bool = {
      Game1.m0 <- m0;
      Game1.m1 <- m1;
      RO.init();
      B_O.x <@ B(RO,Awrap(A)).find(pk,c);
      nobias <$ {0,1};
      return if !(m0 <> m1 /\ (m0 = B_O.x \/ m1 = B_O.x)) 
             then nobias 
             else if m1 = B_O.x then true else false;
  }

}.

(* We use this auxilliary game, which is equivalent to the other one,
   to reason about what happens when the reduction does not try to
   win KPA. In this case its advantage is exactly 1/2. *)

module Aux(B : B_t, A : OWAdv)  = {
  proc main0()  = {
      var pk, m0, m1, mb, r, c;
      pk <$ kgen;
      m0 <$ md;
      m1 <$ md;
      INDKPA.b <$ {0,1};
      mb <- if INDKPA.b then m1 else m0;
      r <$ rd;
      c <- enc pk mb r;
      Game1.m0 <- m0;
      Game1.m1 <- m1;
      RO.init();
      B_O.x <@ B(RO,Awrap(A)).find(pk,c);
  }

  proc main() : bool = {
      main0();
      Reduction.nobias <$ {0,1};
      return INDKPA.b = if !(Game1.m0 <> Game1.m1 /\ 
                             ((Game1.m0 = B_O.x \/ Game1.m1 = B_O.x)))
             then Reduction.nobias 
             else if Game1.m1 = B_O.x then true else false;
  }

}.

(* We use this auxilliary game, which is equivalent to the one in
   which B is run to reason about distributions over functions
   and different ways of generating them. *)
module B_OA(B : B_t, A : A_t) = {
  proc main() : bool = {
     var pk,c,r;
     I.b <$ {0,1};
     pk <$ kgen;
     if (I.b) { Game1.m0 <$ md; Game1.m1 <$ md; Game1.mb <- Game1.m1; }
     else { Game1.m0 <$ md; Game1.m1 <$ md; Game1.mb <- Game1.m0; }
     r <$ rd;
     c <- enc pk Game1.mb r;
     G.g <$ hd;
     G.rep <- witness;
     G.inS <- fun m' => false;
     B_O.x <@ B(H(I),A).find(pk,c);
     return (B_O.x = Game1.m0 \/ B_O.x = Game1.m1);
  }
}.

op eps_msg = 1%r / (size ((Finite.to_seq (support md))))%r.

section.

declare module A <: OWAdv{-RO, -Game1, -INDKPA, -G, -H, -I, -Reduction, -Game1, -Reduction}.

declare module B <: B_t {+Awrap(A)}.

equiv auxgood : 
   INDKPA(Reduction(B,A)).main ~ Aux(B,A).main : ={glob A, glob B} ==> 
          ={glob RO, glob Reduction, Game1.m0, Game1.m1, B_O.x, INDKPA.b, res}.
proc;inline *; wp; rnd; call(_: ={glob RO}); 1,2: by sim.
conseq />; 1: smt().
by auto => />.  
qed.

module Bridge = {
  var rand0 : rand
  var rand1 : rand
  var h : msg -> rand
  var g : msg -> rand
  var r : rand

   proc bL(side : bool, m0 : msg,m1 : msg) = {
      h <$ hd;
      rand0 <$ rd;
      rand1 <$ rd;
      r <- h (if side then m1 else m0);
      g <- fun (x : msg) =>
         if x = m0 \/ x = m1 then if x = m0 then rand0 else rand1
    else h x;
  }

   proc bR() = {
     r <$ rd;
     g <$ hd;
   }
}.

equiv bridge _b _m0 _m1 : Bridge.bL ~ Bridge.bR : arg{1} = (_b,_m0,_m1) ==> 
  Bridge.r{2} = Bridge.h{1} (if _b then _m1 else _m0) /\
  Bridge.g{2} =
  fun (x : msg) =>
    if x = _m0 \/ x = _m1 then if x = _m0 then Bridge.rand0{1} else Bridge.rand1{1}
    else Bridge.h{1} x.
admitted.

equiv BO2BOA :
    B_O(H(I),B,Awrap(A)).main ~ B_OA(B,Awrap(A)).main :
       ={glob B, glob A} ==> ={I.b,Game1.m0, Game1.m1, Game1.mb,B_O.x,res} /\ 
        (res{1} = G.inS{1} B_O.x{1}) /\
        (G.inS{1} = fun x => (x = Game1.m0{2} \/ x = Game1.m1{2})).
proc;inline *; conseq />.
call(_: (fun x => if G.inS{1} x then G.rep{1} x else G.g{1} x) =
        (fun x => if G.inS{2} x then G.rep{2} x else G.g{2} x) ); 1,2: by  proc;auto => /> /#.
sp;seq 1 1 : (#pre /\ ={I.b}); 1: by auto.
case (I.b{2}).
+ rcondt{2} 2; 1: by move => *;auto.
  swap {1} [2..5] -1.
  seq 3 3 : (#pre /\ ={pk,Game1.m0,Game1.m1}); 1: by auto => />.
  sp;swap {1} 2 2; swap {2} 2 1; wp; conseq />.
  transitivity {1} { Bridge.bL(true,Game1.m0,Game1.m1); } 
     (true ==> h{1} = Bridge.h{2} /\ rand0{1} = Bridge.rand0{2} /\ rand1{1} = Bridge.rand1{2} )
     ( ={Game1.m0,Game1.m1} ==> r{2} = Bridge.h{1} Game1.m1{2} /\
      G.g{2} = (fun (x : msg) =>
        if x = Game1.m0{2} \/ x = Game1.m1{2} then if x = Game1.m0{2} then Bridge.rand0{1} else Bridge.rand1{1} else Bridge.h{1} x)); 1,2: smt().
  + by inline *; auto => />.
  transitivity {2} { Bridge.bR(); } 
     ( ={Game1.m0,Game1.m1} ==> Bridge.r{2} = Bridge.h{1} Game1.m1{2} /\ ={Game1.m0,Game1.m1} /\
      Bridge.g{2} = (fun (x : msg) =>
        if x = Game1.m0{2} \/ x = Game1.m1{2} then if x = Game1.m0{2} then Bridge.rand0{1} else Bridge.rand1{1} else Bridge.h{1} x)) 
     (={Game1.m0,Game1.m1} ==> Bridge.g{1} = G.g{2} /\ Bridge.r{1} = r{2} /\ ={Game1.m0,Game1.m1} ); 1,2:  smt(). 
   conseq />; ecall (bridge true Game1.m0{1} Game1.m1{1}); auto => />. 
  + by inline *; auto => />.
rcondf{2} 2; 1: by move => *;auto.
swap {1} [2..5] -1.
seq 3 3 : (#pre /\ ={pk,Game1.m0,Game1.m1}); 1: by auto => />.
sp;swap {1} 2 2; swap {2} 2 1; wp; conseq />.
  transitivity {1} { Bridge.bL(false,Game1.m0,Game1.m1); } 
     (true ==> h{1} = Bridge.h{2} /\ rand0{1} = Bridge.rand0{2} /\ rand1{1} = Bridge.rand1{2} )
     ( ={Game1.m0,Game1.m1} ==> r{2} = Bridge.h{1} Game1.m0{2} /\
      G.g{2} = (fun (x : msg) =>
        if x = Game1.m0{2} \/ x = Game1.m1{2} then if x = Game1.m0{2} then Bridge.rand0{1} else Bridge.rand1{1} else Bridge.h{1} x)); 1,2: smt().
  + by inline *; auto => />.
  transitivity {2} { Bridge.bR(); } 
     ( ={Game1.m0,Game1.m1} ==> Bridge.r{2} = Bridge.h{1} Game1.m0{2} /\ ={Game1.m0,Game1.m1} /\
      Bridge.g{2} = (fun (x : msg) =>
        if x = Game1.m0{2} \/ x = Game1.m1{2} then if x = Game1.m0{2} then Bridge.rand0{1} else Bridge.rand1{1} else Bridge.h{1} x)) 
     (={Game1.m0,Game1.m1} ==> Bridge.g{1} = G.g{2} /\ Bridge.r{1} = r{2} /\ ={Game1.m0,Game1.m1} ); 1,2:  smt(). 
   conseq />; ecall (bridge false Game1.m0{1} Game1.m1{1}); auto => />.
  + by inline *; auto => />.
qed.

(* We first show that B is actually solving OW except with negligible probability,
   as m_!b is information-theoretically hidden. Furthermore, we exclude the
   case where m1 = m0, as in this case our reduction does nothing. *)

lemma refine_game &m :
 `|   Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res ] -  
    Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res /\ (I.b = (Game1.m1 = B_O.x)) ] | <= eps_msg.
have H : 
   Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res /\ 
                                          (I.b <> (Game1.m1 = B_O.x)) ] <= eps_msg; last first.
+ have : `|Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res ] -
  Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res /\ (I.b = (Game1.m1 = B_O.x))]| <=
       Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res /\  (I.b <> (Game1.m1 = B_O.x)) ]; last by smt().
  byequiv : ((G.inS B_O.x) /\
                    (I.b <> (Game1.m1 = B_O.x))) => //.
  proc; conseq />; 1: smt().
  inline *; call(_: ={glob H}); 1,2: by sim.
  by auto => /> /#.
have -> : 
   Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res  /\ I.b <> (Game1.m1 = B_O.x)] = 
   Pr[B_OA(B, Awrap(A)).main() @ &m : res /\ I.b <> (Game1.m1 = B_O.x)]
     by byequiv (BO2BOA) => //. 
byphoare => //;proc;inline *.
seq 1 : #pre (eps_msg); 1: by auto.
+ auto => />. 
  rewrite dbool_ll.
  move : (RField.unitrE eps_msg).  
  rewrite RField.mulf_neq0 => //. 
  + apply  RField.unitrV. 
    have : exists x, x \in (Finite.to_seq (support md)); last by smt(@List).
    exists witness;by smt(md_ll md_funi Finite.mem_to_seq @Distr).
   by smt().
+ case(I.b).
  + rcondt 2; 1: by move => *;auto.
    swap 2 8;rnd (fun m => m = B_O.x).
    call(_: true); 1,2: by auto => />.
    auto => /> => ?????????? m'.
    split; last by smt().
    have -> : mu md (transpose (=) m') = eps_msg; last by smt().
    rewrite /eps_msg mu1_uni_ll; 1: by apply (funi_uni); apply md_funi. 
    + apply md_ll.
    by smt(funi_ll_full md_funi md_ll mu1_uni_ll funi_uni).
  + rcondf 2; 1: by move => *;auto.
    swap 3 7;rnd (fun m => m = B_O.x).
    call(_: true); 1,2: by auto => />.
    auto => /> => ?????????? m'.
    split; last by smt().
    have -> : mu md (transpose (=) m') = eps_msg; last by smt().
    rewrite /eps_msg mu1_uni_ll; 1: by apply (funi_uni); apply md_funi. 
    + apply md_ll.
    by smt(funi_ll_full md_funi md_ll mu1_uni_ll funi_uni).
by hoare; auto => />.
by smt(@Real).
qed.
 
lemma bad_msgcol &m : 
  (forall (O0 <: G_t)  (A0 <: A_t),
  islossless O0.o => islossless O0.oC => 
 (forall (O1 <: RO_t), islossless O1.o => islossless O1.oC => islossless A0(O1).run) =>
   islossless B(O0,A0).find) =>
  Pr[ B_O(H(I), B, Awrap(A)).main() @ &m :  Game1.m0 = Game1.m1 ] =  eps_msg.
proof.
move => B_ll.
byphoare => //; proc; inline *.
seq 4 : #pre (eps_msg) => //. 
+ auto => />. 
  have -> : eps_msg / eps_msg = 1%r. 
  + rewrite -RField.unitrE /eps_msg. 
    apply RField.mulf_neq0 => //. 
    apply  RField.unitrV. 
    have : exists x, x \in (Finite.to_seq (support md)); last by smt(@List).
    exists witness;by smt(md_ll md_funi Finite.mem_to_seq @Distr).
  by smt(dbool_ll dfun_ll rd_ll kgen_ll md_ll).
+ seq 2 : (#pre /\ (Game1.m0 = Game1.m1)) (eps_msg) (1%r) (1%r - eps_msg) (0%r) => //.  
  + rnd (fun m => m = Game1.m0); auto => />.
    + rewrite md_ll /= => v Hv _. 
      rewrite /eps_msg (mu1_uni_ll md v).
      + by apply funi_uni; apply md_funi. 
      + by apply md_ll. 
      by smt().
  + call(_: Game1.m0 = Game1.m1).
    + move => O Ap.
      + by admit. (* FIXME: We are passing an incomplete functor. What should we say about this? *) 
      + by conseq />;islossless.
      + by conseq />;islossless.
      + by auto => />; rewrite rd_ll /=.
  + hoare; auto => />. 
    by call(_: true); auto => />. 
by smt(@Real).
qed.

lemma refine_game_more &m:   
  (forall (O0 <: G_t) (A0 <: A_t),
  islossless O0.o => islossless O0.oC => 
 (forall (O1 <: RO_t), islossless O1.o => islossless O1.oC => islossless A0(O1).run) =>
   islossless B(O0,A0).find) =>

   `|  Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res /\ (I.b = (Game1.m1 = B_O.x)) ]  -
       Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res /\ (I.b = (Game1.m1 = B_O.x)) /\
               Game1.m0 <> Game1.m1] | <= eps_msg.
move => B_ll.
rewrite -(bad_msgcol &m B_ll).
byequiv : (Game1.m0 = Game1.m1) => //.
proc; inline *; call(_: ={glob G}); 1,2: by sim.
by auto => />.
qed.

lemma hop2 &m:   
  (forall (O0 <: G_t) (A0 <: A_t),
  islossless O0.o => islossless O0.oC => 
 (forall (O1 <: RO_t), islossless O1.o => islossless O1.oC => islossless A0(O1).run) =>
   islossless B(O0,A0).find) =>

   `|  Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res ]  -
       Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res /\ (I.b = (Game1.m1 = B_O.x)) /\
               Game1.m0 <> Game1.m1] |  <= 2%r*eps_msg.
proof.
move => B_ll.
have := refine_game &m.
have := refine_game_more &m B_ll.
by smt().
qed.

(* The games match whenever the reduction tries to win KPA *)

lemma matchgames &m : 
   Pr [ INDKPA(Reduction(B,A)).main() @ &m : res /\ 
               Game1.m0 <> Game1.m1 /\ (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x) ] = 
   Pr[ B_O(H(I), B, Awrap(A)).main() @ &m :  res /\ 
               Game1.m0 <> Game1.m1 /\ I.b = (Game1.m1 = B_O.x) ].
have -> :
   Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res /\ 
               Game1.m0 <> Game1.m1 /\ I.b = (Game1.m1 = B_O.x)  ] = 
   Pr[B_OA(B, Awrap(A)).main() @ &m : res /\ 
               Game1.m0 <> Game1.m1 /\ I.b = (Game1.m1 = B_O.x) ]
     by byequiv (BO2BOA) => //. 
have -> :
   Pr[B_OA(B, Awrap(A)).main() @ &m : res /\ 
               Game1.m0 <> Game1.m1 /\ I.b = (Game1.m1 = B_O.x) ]= 
   Pr [ INDKPA(Reduction(B,A)).main() @ &m : res /\
            Game1.m0 <> Game1.m1 /\ (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x) ].
+ byequiv => //.
  proc;inline *; swap {2} 4 -3; seq 1 1 : (#pre /\ I.b{1} = INDKPA.b{2}); 1 : by auto. 
  case (I.b{1}).
  + rcondt {1} 2; 1: by move => *;auto.
    wp;rnd{2}; call(_: (fun x => if G.inS{1} x then G.rep{1} x else G.g{1} x) = RO.h{2}); 1,2: by proc;auto.
    auto => /> /#.
  rcondf {1} 2; 1: by move => *;auto.
  wp;rnd{2}; call(_: (fun x => if G.inS{1} x then G.rep{1} x else G.g{1} x) = RO.h{2}); 1,2: by proc;auto.
  by auto => /> /#.
done.
qed.

(* We can rewrite the KPA advantage as something that is statistically close
   to the refined B_O game, plus 1/2 the probability of reduction  trying to win the KPA game *) 

lemma reasoning &m :
  (forall (O0 <: RO_t), islossless O0.o => islossless O0.oC => islossless A(O0).find) =>
  (forall (O0 <: G_t) (A0 <: A_t),
  islossless O0.o => islossless O0.oC => 
 (forall (O1 <: RO_t), islossless O1.o => islossless O1.oC => islossless A0(O1).run) =>
   islossless B(O0,A0).find) => 
  Pr [ INDKPA(Reduction(B,A)).main() @ &m : res] - 1%r/2%r =
         Pr[ B_O(H(I), B, Awrap(A)).main() @ &m :  res /\ 
               Game1.m0 <> Game1.m1 /\ I.b = (Game1.m1 = B_O.x) ] -
          1%r/2%r * Pr [ INDKPA(Reduction(B,A)).main() @ &m : 
             Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x) ].
proof. 
move => A_ll B_ll.
rewrite -matchgames.
rewrite Pr[mu_split (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))].
have -> : Pr[INDKPA(Reduction(B,A)).main() @ &m : res /\ 
         ! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))] = 
     Pr[INDKPA(Reduction(B,A)).main() @ &m : INDKPA.b = Reduction.nobias /\ 
              ! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))].
+ byequiv => //.
  proc;inline *.
  wp;rnd;call(_: ={glob RO}); 1,2: by sim.
  by auto => />.  
pose e := Pr[INDKPA(Reduction(B,A)).main() @ &m :
      ! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))].
have -> : 
Pr[INDKPA(Reduction(B,A)).main() @ &m :
   INDKPA.b = Reduction.nobias /\ ! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))] = 1%r/2%r * e.
case (e = 0%r); 1: smt(@Distr).
move => *.
have -> : 
  Pr[INDKPA(Reduction(B,A)).main() @ &m :
   INDKPA.b = Reduction.nobias /\ ! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))] =
  Pr[ Aux(B,A).main() @ &m :
   INDKPA.b = Reduction.nobias /\ ! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))] by byequiv auxgood.
move => *.
+ byphoare (_: (glob B) = (glob B){m} /\ (glob A) = (glob A){m} ==> _) => //; proc.
  seq  1: (! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x)))
        (e) (1%r/2%r)
        _ 0%r => //.
  + call (_: (glob B) = (glob B){m} /\ (glob A) = (glob A){m} ==> 
         ! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))).
    bypr=> &m0 @/e [#] eq_globs1 eqglobs2. 
    byequiv (_: _   ==> ={Game1.m0, Game1.m1, B_O.x}) => //.
    proc;inline *; wp; rnd{2}; call(_: ={glob RO}); 1,2: by sim.
    auto => /> //.
  + done.
  + by conseq />;rnd(fun m => m = INDKPA.b); skip;smt(@DBool).
  + by hoare;auto => />.
have ? : 
  Pr[INDKPA(Reduction(B,A)).main() @ &m : ! (Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x))] =
1%r  - Pr[INDKPA(Reduction(B,A)).main() @ &m : Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x)].
+ rewrite Pr[mu_not].
  have -> : Pr[INDKPA(Reduction(B,A)).main() @ &m : true]  = 1%r.
  byphoare => //; islossless; apply (B_ll RO (Awrap(A))); 1,2: by islossless.
  move => O1 O1ll O1cll;islossless.
  + by apply (A_ll O1 O1ll O1cll).
done.
by smt().
qed.

(* Not by accident, we can match the probability that the reduction tries to
   win the game exactly to the probability of winning in the non-refined game. *)

lemma loopback &m :
  (forall (O0 <: RO_t), islossless O0.o => islossless O0.oC => islossless A(O0).find) =>
  (forall (O0 <: G_t) (A0 <: A_t),
  islossless O0.o => islossless O0.oC => 
 (forall (O1 <: RO_t), islossless O1.o => islossless O1.oC => islossless A0(O1).run) =>
   islossless B(O0,A0).find) => 
 `| Pr [ INDKPA(Reduction(B,A)).main() @ &m :  Game1.m0 <> Game1.m1 /\ 
               (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x )] -
    Pr[ B_O(H(I), B, Awrap(A)).main() @ &m : res ] | <= eps_msg.
move => A_ll B_ll.
have -> :
   Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res ] = 
   Pr[B_OA(B, Awrap(A)).main() @ &m : res  ]
     by byequiv (BO2BOA) => //. 
have -> : eps_msg = Pr[B_OA(B, Awrap(A)).main() @ &m :  Game1.m0 = Game1.m1].
+ have <- : Pr[B_O(H(I),B, Awrap(A)).main() @ &m : Game1.m0 = Game1.m1] =
            Pr[B_OA(B, Awrap(A)).main() @ &m : Game1.m0 = Game1.m1]
     by byequiv (BO2BOA) => //. 
by rewrite (bad_msgcol &m).
byequiv : (Game1.m0 = Game1.m1) => //.
proc;inline *; swap {1} 4 -3; seq 1 1 : (#pre /\ I.b{2} = INDKPA.b{1}); 1 : by auto. 
case (I.b{2}).
+ rcondt {2} 2; 1: by move => *;auto.
  wp;rnd{1}; call(_: (fun x => if G.inS{2} x then G.rep{2} x else G.g{2} x) = RO.h{1}); 1,2: by proc;auto.
  by auto => /> /#.
rcondf {2} 2; 1: by move => *;auto.
wp;rnd{1}; call(_: (fun x => if G.inS{2} x then G.rep{2} x else G.g{2} x) = RO.h{1}); 1,2: by proc;auto.
by auto => /> /#.
qed.

lemma reduction_works &m :
  (forall (O0 <: RO_t), islossless O0.o => islossless O0.oC => islossless A(O0).find) =>
  (forall (O0 <: G_t) (A0 <: A_t),
  islossless O0.o => islossless O0.oC => 
 (forall (O1 <: RO_t), islossless O1.o => islossless O1.oC => islossless A0(O1).run) =>
   islossless B(O0,A0).find) => 
   Pr[  B_O(H(I), B, Awrap(A)).main() @ &m : res ] <= 
    2%r * (`| Pr [ INDKPA(Reduction(B,A)).main() @ &m : res] - 1%r/2%r |) + 5%r * eps_msg.
proof. 
move => A_ll B_ll.
have  := (hop2 &m B_ll).
rewrite (reasoning &m A_ll B_ll).
have := (loopback &m A_ll B_ll). 
pose x := Pr[INDKPA(Reduction(B, A)).main() @ &m : Game1.m0 <> Game1.m1 /\ (Game1.m0 = B_O.x \/ Game1.m1 = B_O.x)] .
pose y := Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res].
pose z := Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res /\ I.b = (Game1.m1 = B_O.x) /\ Game1.m0 <> Game1.m1].
have -> : Pr[B_O(H(I), B, Awrap(A)).main() @ &m : res /\ Game1.m0 <> Game1.m1 /\ I.b = (Game1.m1 = B_O.x)] = z by smt().
smt().
qed.

end section.

section.

declare module A <: OWAdv{-RO, -Game1, -INDKPA, -G, -H, -I, -Reduction, -Game1, -Reduction}.

axiom A_ll (O <: RO_t) : islossless O.o => islossless O.oC => islossless A(O).find.

(* If we plug everything together we get the bound 
   Note that, because we always have to use the probability of
   and not directly the probability of find, we always get an
   extra d factor. *)

lemma main_theorem &m d : 
  0 <= d =>
  (forall (O <: RO_t), islossless O.o => islossless O.oC => islossless A(O).find) =>
    (forall (O <: Gi_t), hoare[ A_O(Awrap(A), Count(O)).main : true ==> Count.ch <= d]) =>  
  exists (B <: B_t{+Awrap(A)}),
  (forall (O0 <: G_t) (A0 <: A_t),
  islossless O0.o => islossless O0.oC => 
 (forall (O1 <: RO_t), islossless O1.o => islossless O1.oC => islossless A0(O1).run) =>
    islossless B(O0, A0).find) /\
  Pr[ OW(A).main() @ &m : res ] <= 
        (2%r * (d%r + 1%r))^2 * (2%r * `| Pr [ INDKPA(Reduction(B,A)).main() @ &m : res] - 1%r/2%r | + 
           5%r * eps_msg).
move => d_ge0 A_ll A_bnd. 
have [B [#] B_ll H0] := (ow2h_hop (A) &m d d_ge0 A_ll A_bnd).
exists B; split.
+ move => O A0 O_ll Oc_ll A0_ll. apply (B_ll O A0 O_ll Oc_ll _).
  + by move => O0 O0ll O0cll; apply (A0_ll O0 O0ll O0cll).
have H2 := (reduction_works A  B &m A_ll _). 
+ move => O A0 O_ll Oc_ll A0_ll. apply (B_ll O A0 O_ll Oc_ll _).
  + by move => O0 O0ll O0cll; apply (A0_ll O0 O0ll O0cll).
by smt(@StdOrder.RealOrder mu_bounded).
qed. 

end section.

