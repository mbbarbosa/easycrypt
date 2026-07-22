require import AllCore RealExp Distr DBool List FinType.
require (****) T_OW2H T_OWPKE.

clone import T_OWPKE as OWPKE.
import MUniFinFun.
(**************************************************************)
(*                                                            *)
(*                   Security Proof                           *)
(*                                                            *)
(**************************************************************)

(* Game 1 is OW game but we sample the randomness from
   an independent source. *)

module Game1(A : OWAdv_ROM)  = {
   var m', m : msg
   proc main() = {
      var pk, c,  r, rs;
      RO.init();
      pk <$ kgen;
      m <$ md;
      r <- RO.h m; 
      c <- enc pk m r;
      rs <$ rd;
      RO.h <- fun ms => if ms = m then rs else RO.h ms;
      m' <@ A(RO).find(pk,c);
      return (m' = m);
   }
}.

(* We now use the semi classical lemma to bound the distance to Game 1. *)

clone import T_OW2H as OW2H with
  type X <- msg,
  type Y <- rand,
  type Z <- pkey * cph,
  type W <- msg.
import SemiClassical.

(* This defines the joint distribution that we will
   use to hop from Game1 to Game2. 
   To explore for better bound: don't puncture if m0 = m1. *)
module I : Init = {
  var b : bool
  proc prm() : (msg -> rand) * 
               (msg -> rand) * (msg -> bool) * 
               (pkey * cph) * (msg -> bool) = {
     var pk,c,h,rs,sf;
     h <$ hd;
     pk <$ kgen;
     Game1.m <$ md;
     c <- enc pk Game1.m (h Game1.m);     
     rs <$ rd; 
     sf <- fun _ => rs;
     return (h, sf, 
                fun ms => ms = Game1.m, 
     (pk, c), fun ms => ms = Game1.m);
  }
}.

(* We take the OW adversary and we transform it into an
   attacker against I.  *)
module Awrap(A : OWAdv_ROM, O : G_t) = {
   proc run(pk : pkey, c : cph) : msg = {
      Game1.m' <@ A(O).find(pk,c);
      return Game1.m';
   }
}.


lemma ow2h_hop (A <: OWAdv_ROM {-RO, -G, -H, -I, -Game1}) &m : 
  `| Pr [ OW_ROM(A).main() @ &m : res  ] -
              Pr [ Game1(A).main() @ &m : res] | =
  `| Pr [ A_O(Awrap(A),G(I)).main() @ &m : res]  - 
              Pr [ A_O(Awrap(A),H(I)).main() @ &m : res] |.
proof. 
have -> : Pr [ OW_ROM(A).main() @ &m : res ] = 
          Pr [ A_O(Awrap(A),G(I)).main() @ &m : res].
+ byequiv => //.
  proc;inline*;auto => />.
  call(_: RO.h{1} = G.g{2}); first by sim.
  auto => />; 1:smt().
  by rnd{2}; auto => /> /#.
have -> : Pr [ Game1(A).main() @ &m : res] = 
          Pr [ A_O(Awrap(A),H(I)).main() @ &m : res].
+ byequiv => //.
  proc;inline*;auto => />.
  call(_: RO.h{1} = fun x => if G.inS{2} x then G.rep{2} x else G.g{2} x); 
     first by proc; auto => />.
  by auto => /> /#.
done.
qed.

(* The proof is completed with two reductions to OW, which are
   very similar. One shows Game1 can be reduced to OW, and the
   other one shows OW2H B is also a OW attacker. *)

module Reduction(A : OWAdv_ROM) : OWAdv  = {
  proc find(pk : pkey, c : cph) : msg = {
      RO.init();
      Game1.m' <@ A(RO).find(pk,c);
      return Game1.m';
  }

}.

section.

declare module A <: OWAdv_ROM {-Game1}.

lemma dist_match m: 
  (dlet hd
     (fun (h : msg -> rand) =>
        dmap rd (fun (rs0 : rand) => (fun (ms : msg) => if ms = m then rs0 else h ms, h m)))) =
  (dlet hd (fun (h : msg -> rand) => dmap rd (fun (r0 : rand) => (h, r0)))).
proof.
have  /= <- := dmap_dprodE_swap rd hd (fun (hr : _ * _) => (hr.`2,hr.`1)).
have  /= <- := dmap_dprodE_swap rd hd (fun (hr : _ * _) => (fun ms => if ms = m then hr.`1 else hr.`2 ms, hr.`2 m)).
rewrite /hd {2}(dfun_dmap_up (fun _ => rd) m) /= -/hd; 1: by apply rd_ll.
rewrite -{2}(dmap_id rd) dmap_dprod /= dmap_comp  /= /(\o) /=.
rewrite dprodA dmap_comp  /= /(\o) /=.
rewrite (dprodC (rd `*` hd)) dmap_comp  /= /(\o) /=.
rewrite {2}(dprodC rd hd). 
rewrite -{2}(dmap_id rd) dmap_dprod /= dmap_comp  /= /(\o) /=.
rewrite !dmap_dprodE; congr => /=; apply fun_ext => r.
have  /= := dmap_comp (fun (hr : _*_) => (fun ms => if m = ms then hr.`2 else hr.`1 ms)) (fun (y : msg -> rand) => (fun (ms : msg) => if m = ms then r else y ms, y m)) (hd `*` rd) .
rewrite /(\o) /=.
have -> : (fun (x : (msg -> rand) * rand) => (fun (ms : msg) => if m = ms then r else if m = ms then x.`2 else x.`1 ms, x.`2)) = 
(fun (y : (msg -> rand) * rand) => (fun (x' : msg) => if m = x' then r else y.`1 x', y.`2)) by apply fun_ext => x /#.
move => <-.
have  /=  <- := dfun_dmap_up (fun _ => rd) m _ => /=; 1: by apply rd_ll.
by rewrite -/hd;congr; rewrite fun_ext => */#.
qed.

(* The games match whenever the reduction tries to win KPA *)
lemma reduction_works &m : 
   (forall (O <: RO_t), islossless O.o => islossless A(O).find) =>
     Pr [ OW(Reduction(A)).main() @ &m : res ] = 
      Pr [ Game1(A).main() @ &m : res ].
proof.
move => A_ll. 
byequiv => //. 
proc; inline *.
swap{2} [2..3] -1; seq 2 2 : (#pre /\ ={pk} /\ m{1} = Game1.m{2}); 1: by auto.
swap {1} 5 -4;swap{2} 4 -2. 
wp;call(_: ={glob RO}); 1: by sim.
swap {1} 3 1; swap {2} 4 1.
wp 2 4; conseq (_: ={r,RO.h});1: smt().
rnd : *0 *0; auto => />. 
by move => &2;rewrite dist_match //=.
qed.

end section.

(* Now we complete the proof by relating the probability that the
  adversary B works in the SC lemma to OW security; this
  argument is very similar to the one above *)
module Reduction2(B : B_t, A : OWAdv_ROM) : OWAdv  = {
  var r : rand (* for transitivity *)
  proc find(pk : pkey, c : cph) : msg = {
      RO.init();
      B_O.x <@ B(RO,Awrap(A)).find(pk,c);
      return B_O.x;
  }

}.

section.

declare module A <: OWAdv_ROM.

declare module B <: B_t {+Awrap(A)}.

lemma reduction_works2 &m : 
   Pr [ OW(Reduction2(B,A)).main() @ &m : res ] = 
   Pr[ B_O(H(I), B, Awrap(A)).main() @ &m :  res ].
proof.
byequiv => //. 
proc; inline *.
swap{2} [2..3] -1; seq 2 2 : (#pre /\ ={pk} /\ m{1} = Game1.m{2}); 1: by auto.
swap {1} 5 -4;swap{2} 3 -2. 
wp;call(_: RO.h{1} = fun x => if G.inS{2} x then G.rep{2} x else G.g{2} x ); 1: by proc; auto. 
sp;wp;conseq (: _ ==> r{1} = h{2} Game1.m{2} /\ RO.h{1} = fun (x : msg) => if x = Game1.m{2} then rs{2} else h{2} x); 1: by smt().
transitivity {2} { rs <$ rd;
                   h <$ hd;
                   Reduction2.r <- h Game1.m;
                   h <- fun (x : msg) => if x = Game1.m then rs else h x;}
           (={glob B,pk} /\ m{1} = Game1.m{2} ==> RO.h{1} = h{2} /\ 
                                                  r{1} = Reduction2.r{2})
           (={glob B,pk,Game1.m} ==> Reduction2.r{1} = h{2} Game1.m{2} /\
                     h{1} = fun (x : msg) => if x = Game1.m{2} then rs{2} else h{2} x);1,2,4: by auto => />/#. 
swap {2} 1 1.
rnd : *0 *0; auto => />.
move => &2; rewrite dist_match /=.
by auto => />.
qed.

end section.

(* Main theorem *)

section.

declare module A <: OWAdv_ROM {-Game1, -G, -H, -I,-INDKPA1,-INDKPA0}.

lemma main_theorem_ow &m d : 
  (forall (O <: RO_t), islossless O.o => islossless A(O).find) =>
  (forall (O <: Gi_t), hoare[ A_O(Awrap(A), Count(O)).main : true ==> Count.ch <= d]) =>
  exists (B <: B_t{+Awrap(A)}),
  (forall (O <: RO_t) (A0 <: A_t), islossless O.o => 
   (forall (O0 <: RO_t), islossless O0.o => islossless A0(O0).run)  =>
      islossless B(O, A0).find) /\
  Pr[ OW_ROM(A).main() @ &m : res ] <= 
       Pr [ OW(Reduction(A)).main() @ &m : res]  + 
      4%r * d%r *  sqrt (Pr [ OW(Reduction2(B,A)).main() @ &m : res]).
move => A_ll A_cnt.
have [B [B_ll B_adv]] := (ow2hsc1h (I) (Awrap(A)) &m d _ _).
+ by move => O O_ll;islossless; apply (A_ll O O_ll).
+ by apply A_cnt.
exists B; split. 
+ move => O A0 HO Awll. apply (B_ll O A0); 1: by apply HO.
  + by move => O1; apply (Awll O1).
have H0 := ow2h_hop A &m.
have H1 := reduction_works A &m A_ll.
have H2 := reduction_works2 A B &m.
by smt().
qed. 

op eps_msg = mu1 md witness.

lemma main_theorem &m d : 
  0 <= d =>
  (forall (O <: RO_t), islossless O.o => islossless A(O).find) =>
  (forall (O <: Gi_t), hoare[ A_O(Awrap(A), Count(O)).main : true ==> Count.ch <= d]) =>
  exists (B <: B_t{+Awrap(A)}),
  Pr[ OW_ROM(A).main() @ &m : res ] <= 
    2%r * `| Pr [ INDKPA(OWPKE.Reduction(Reduction(A))).main() @ &m : res ] -  1%r/2%r | + 
      4%r * d%r *  
         sqrt (2%r * `| Pr [ INDKPA(OWPKE.Reduction(Reduction2(B,A))).main() @ &m : res ] -  1%r/2%r | + eps_msg) 
             + eps_msg.
proof.
move => d_ge0 A_ll A_cnt.
have [B [B_ll B_adv]]  := main_theorem_ow &m d A_ll A_cnt.
exists B.
have H1 /= := OWPKE.main (Reduction(A)) &m _.
+ islossless;1:by apply (A_ll RO); islossless; rewrite /hd dfun_ll /=; apply rd_ll.
     by rewrite /hd dfun_ll /=;1:by apply rd_ll.
have H2 /= := OWPKE.main (Reduction2(B,A)) &m _.
+ islossless.
  +  apply (B_ll RO (Awrap(A))); 1: by islossless. 
     + move => O0 Ooll; islossless;  apply (A_ll O0 Ooll).
     by rewrite /hd dfun_ll /=;1:by apply rd_ll.
by smt(ge0_sqrt rpow_hmono).
qed.

end section.

