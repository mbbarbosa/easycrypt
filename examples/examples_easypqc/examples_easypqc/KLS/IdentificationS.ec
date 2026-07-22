require import AllCore Int Real List FinType DBool Distr.

theory IDS.
(* Generic types for 
   public and secret key, 
   commitment W, challenge C, response Z, 
   and internal state of the prover
*)
type PK, SK, W, C, Z, Pstate.

type transcript = W*C*Z.

(* -------------------------------------------------------------------------------------------
   
   Identification scheme (protocol between prover and verifier) 
   
   ------------------------------------------------------------------------------------------- *)

(* Generic prover *)
module type Prover = { 
  proc keygen(): PK*SK
  proc commit(sk:SK): W
  proc response(sk:SK, c:C): Z
}. 

(* Generic verifier *)
module type Verifier ={
  proc challenge(w:W, pk:PK): C
  proc verify(pk:PK, w:W, c:C, z:Z): bool
}.


(* ----------------------------------
    Security for IDS 1: Impersonation  
   ----------------------------------*)

(* Impersonator *)
module type Adv_Imp = {
  proc commit(pk:PK): W
  proc response(pk:PK, c:C): Z
}.

(* Impersonation Game *)
module Imp_Game (P: Prover, V: Verifier, A: Adv_Imp) = {

  proc main() = {
    var sk, pk,w,c,z,result;
   
    (pk,sk) <@ P.keygen();
    w <@ A.commit(pk);
    c <@ V.challenge(w,pk);
    z <@ A.response(pk, c);
    result <@ V.verify(pk,w,c,z);
    return result;
  }
}.


(* -----------------------------------------------------
    Security for IDS 2: HonestVerifierZeroKnowledge  
   ----------------------------------------------------- *)


(***********************************************************)
(*     HVZK: There exists an HVZK_Sim such that            *)
(*     HVZK_Sim.getTrace(pk)                               *) 
(*             ~ Honest_Execution.get_trace()              *)
(***********************************************************)

(* Simulator for HVZK that generates valid transcripts given a public key *)
module type HVZK_Sim = {
  proc get_trans(pk:PK) : transcript
}.


(* Module that generates transcripts of honest executions as reference *) 
module Honest_Execution (P: Prover, V: Verifier) = {

  proc get_trans(pk:PK, sk:SK) = {
    var w,c,z;

    w <@ P.commit(sk);
    c <@ V.challenge(w,pk);
    z <@ P.response(sk, c);
    return (w,c,z);
  }
}.

(* Abstract oracle used in the game to give the distinguisher adaptive 
   access to multiple transcripts *) 
module type HVZK_Oracle = {
  proc get_trans() : transcript
}.

 (* Instantiation of the oracle using a Simultor. Note that init 
    only takes a public key *)
module HVZK_Sim_Oracle (Sim :HVZK_Sim) : HVZK_Oracle = {
  var pk : PK
  proc init (pki : PK) : unit = {
    pk <- pki;
  }
  
  proc get_trans() = {
    var trans;
    trans <@ Sim.get_trans(pk);
    return trans;
  }
}.

 (* Instantiation of the oracle using honest execution. Note that 
    init in this case also needs the secret key *)
module HVZK_HE_Oracle (P : Prover, V: Verifier ) : HVZK_Oracle = {
  var pk : PK
  var sk : SK
  proc init (pki : PK, ski : SK) : unit = {
    pk <- pki;
    sk <- ski;
  }
  
  proc get_trans() = {
    var trans;
    trans <@ Honest_Execution(P,V).get_trans(pk,sk);
    return trans;
  }
}.

 (* abstract adversary type *)
qmodule type HVZK_Distinguisher (O: HVZK_Oracle) = {
  proc distinguish (pk : PK): bool
}.

 (* actual distinguishing game *)
module HVZK_Game (Sim: HVZK_Sim, P: Prover, V: Verifier, D: HVZK_Distinguisher) = {
  module OSim = HVZK_Sim_Oracle(Sim)
  module OHE = HVZK_HE_Oracle(P,V)
 
  proc main(n: int, b:bool) = {
    var sk, pk, result;
    
    (pk, sk) <@ P.keygen();
    if(b) {
      OSim.init(pk);
      result <@ D(OSim).distinguish(pk); 
    } else {
      OHE.init(pk, sk);
      result <@ D(OHE).distinguish(pk); 
    }
    return result;
  }
}.


end IDS.

theory ComRecIDS.
clone import IDS.

op recCom (pk:PK, c: C, z : Z) : W.

axiom recovering (P <: Prover) (V <: Verifier) (pk:PK) (sk:SK) &m:  
  Pr[P.keygen() @ &m : res = (pk, sk)] > 0%r
   => Pr[Honest_Execution(P, V).get_trans(pk, sk) @ &m : let (w,c,z) = res in w = recCom pk c z] = 1%r.
end ComRecIDS.


theory LossyIDS.
clone import IDS.

clone import FinType as FinW with 
   type t <- W.

clone import FinType as FinPK with 
   type t <- PK.

clone import FinType as FinZ with 
   type t <- Z.
   
   
op verify : PK -> W -> C -> Z -> bool.
op [full uniform lossless]dC : C distr.

module V = { 
  proc challenge(w:W, pk:PK): C = { 
    var c;
    c <$ dC;
    return c;
  }

  proc verify(pk:PK, w:W, c:C, z:Z): bool = {
    return verify pk w c z;
  }
}.


op keygen : (PK * SK) distr.
op commit : SK -> (W * Pstate) distr.
op response : SK -> C -> Pstate -> Z.

module P = {

  var pstate : Pstate

  proc keygen(): PK*SK = { 
    var ks;
    ks <$ keygen;
    return ks;
  } 
  
  proc commit(sk:SK): W = { 
    var w;
    (w, pstate) <$ commit sk;
    return w;
  }
    
  proc response(sk:SK, c:C): Z = {
    return response sk c pstate;
  }

}.




(* separate module to introduce lossy key generation *)
module type LossyKG_t = {
  proc keygen() : PK
}.

(* operator based LossyKG_t  *)
op [lossless]lossy_kg : PK distr.
module L : LossyKG_t = {
  proc keygen() : PK = {
    var pk;
    pk <$ lossy_kg;
    return pk;
  }
}.


(* the distinguisher against the lossy keygen mode *)
qmodule type PK_Distinguisher = {
  proc distinguish (pk: PK) : bool
}.

(* Distinguishing game for lossy keygen mode *) 
module PK_Dist_Game (P:Prover, LKG:LossyKG_t, D:PK_Distinguisher) = {
  proc main(b : bool) : bool = {
    var pk,sk,b';
    if(b) {
      (pk,sk) <@ P.keygen();
    } else {
      pk <@ LKG.keygen();
    }
    b' <@ D.distinguish(pk);
    return b';
  }
}.

(* For any lossy identification scheme there must exist an LKG such
   such that forall distinguishers, the following is small.
(* distignuishing advantage *)
op eps_distinguishing : real.


axiom ind_l_kg (P <: Prover) (LKG <: LossyKG_t) (D <: PK_Distinguisher)  &m :
  `|Pr[PK_Dist_Game (P, LKG, D).main(true) @ &m : res] 
  - Pr[PK_Dist_Game (P, LKG, D).main(false) @ &m : res]| 
  <= eps_distinguishing.
*)
(* TODO: Define statistical imp advantage bound *)  


(* Impersonation Game *)
module LossyImp_Game (LKG : LossyKG_t, V: Verifier, A: Adv_Imp) = {

  (* game for given pk *)
  proc main_pk (pk : PK) = {
    var w,c,z,result;
   
    w <@ A.commit(pk);
    c <@ V.challenge(w,pk);
    z <@ A.response(pk, c);
    result <@ V.verify(pk,w,c,z);
    return result;
  }

  (* standard game *)
  proc main() = {
    var pk,result;
   
    pk <@ LKG.keygen();
    result <@ main_pk(pk);
    return result;
  }
}.

op [a u] max_pw(du : 'u distr, E : W -> 'u -> bool, ws : W list) =
    (foldr 
      (fun (w : W) (prevm : (real * W)) => if prevm.`1 < mu du (E w) 
                                           then (mu du (E w),w) 
                                           else prevm) 
            (mu du (fun c => E (head witness ws) c),head witness ws) (behead ws)).

op [a u] max_prob(du : 'u distr, E : W -> 'u -> bool, ws : W list) = (max_pw du E ws).`1.
op [a u] max_w(du : 'u distr, E : W -> 'u -> bool, ws : W list) = (max_pw du E ws).`2.

lemma max_prob_bounded(du : 'u distr) E ws :  
  ws <> [] =>  0%r <= max_prob du E ws <= 1%r
 by rewrite  /max_prob /max_pw; move => wsne; elim (behead ws) => //=; smt(mu_bounded).

lemma max_w_prob (du : 'u distr) E ws :
    ws <> [] =>
    mu du (fun c => E (max_w du E ws) c) = max_prob du E ws
 by rewrite /max_w /max_prob /max_pw; move => wsne; elim (behead ws) => //= /#.

import Biased.

module ExpImp(LKG : LossyKG_t)= {
   proc epsmax_pk(pk : PK) = {
       var epsmax;
       epsmax <- max_prob dC
            (fun (w : W) (c : C) => has (verify pk w c) FinZ.enum) FinW.enum;
       return epsmax;
   }
   proc epsmax_pk_b(pk : PK) = {
       var b,epsmax;
       epsmax <@ epsmax_pk(pk);
       b <$ dbiased epsmax;
       return b;
   }    
   (* compute epsmax and sample a bit according to it *)
   proc epsmax_b() = {
       var pk,b;
       pk <@ LKG.keygen();
       b <@ epsmax_pk_b(pk);
       return b;
   }
}.

lemma eps_max_val_ph _pk (LKG <: LossyKG_t):
  phoare [  ExpImp(LKG).epsmax_pk_b : pk = _pk ==> res] =
     (max_prob dC
          (fun (w : W) (c : C) => has (verify _pk w c) FinZ.enum) FinW.enum).
proof.
proc; inline *; rnd; auto => />.
rewrite dbiasedE /=; 1: by rewrite clamp_id //; apply max_prob_bounded; smt(in_nil FinW.enumP).
qed.

lemma eps_max_val _pk (LKG <: LossyKG_t) &m:
  Pr[ExpImp(LKG).epsmax_pk_b(_pk) @ &m : res] =
     max_prob dC
                 (fun (w : W) (c : C) => has (verify _pk w c) FinZ.enum) FinW.enum.
proof.
byphoare (_: pk = _pk ==> res) => //.
apply (eps_max_val_ph _pk (LKG)).
qed.

module C : Adv_Imp = {
   proc commit(pk : PK) = {
       var wmax;
       wmax <- max_w dC
                 (fun (w : W) (c : C) => has (verify pk w c) FinZ.enum) FinW.enum;
       return wmax;
        
   }
   proc response(pk : PK, c : C) = {
       var wmax, z;
       wmax <- max_w dC
                 (fun (w : W) (c : C) => has (verify pk w c) FinZ.enum) FinW.enum;
       z <- head witness (filter (fun z => verify pk wmax c z) FinZ.enum);
       return z;
        
   }

}.

(* For information theoretic adversaries, the success probability in winning the imp game is 
   exactly epsmax. *)
lemma tight_upper_bound &m (LKG <: LossyKG_t) :
     Pr[ LossyImp_Game (LKG,V,C).main() @ &m : res ] =
          Pr[ ExpImp(LKG).epsmax_b() @ &m : res ].
byequiv => //.
proc; seq 1 1 : (={glob LKG, pk}); 1: by  call(_: true);  auto => /> /#.
call (: ={arg} ==> ={res}) => //.
bypr (res{1}) (res{2}) => //.
move => &1 &2 _b eqarg.
have HA : Pr[LossyImp_Game(LKG, V, C).main_pk(arg{1}) @ &1 : res] =
     max_prob dC
                 (fun (w : W) (c : C) => has (verify arg{1} w c) FinZ.enum) FinW.enum. 
+ byphoare (_: pk = arg{2} ==> res) => //.
  proc; inline *; swap 6 -5;wp;rnd; auto => />.
  rewrite eqarg.
  rewrite -max_w_prob; 1: by smt(in_nil FinW.enumP).
  apply mu_eq => x /=; apply eq_iff.
  pose ll := filter (verify arg{2} (max_w dC (fun (w : W) (c : C) => has (verify arg{2} w c) FinZ.enum) FinW.enum) x)
        FinZ.enum.
  split.
  + by move => H;rewrite hasP;  exists (head witness ll); rewrite FinZ.enumP /= /#.
  by move => /= /has_count H; have hh : ll <> []; smt(size_filter size_eq0 filter_all mem_head_behead).

have HB := eps_max_val arg{2} LKG &2.

case _b.
+ have -> : Pr[LossyImp_Game(LKG, V, C).main_pk(arg{1}) @ &1 : res = true] = 
            Pr[LossyImp_Game(LKG, V, C).main_pk(arg{1}) @ &1 : res].
  + byequiv => //; conseq (_: ={res}); 1:smt(). 
    by proc;sim. 
  have -> : Pr[ExpImp(LKG).epsmax_pk_b(arg{2}) @ &2 : res = true] = 
            Pr[ExpImp(LKG).epsmax_pk_b(arg{2}) @ &2 : res].
  + byequiv => //; conseq (_: ={res}); 1:smt(). 
    by proc;sim. 
  by move => *; rewrite HA HB eqarg.

have -> : Pr[LossyImp_Game(LKG, V, C).main_pk(arg{1}) @ &1 : res = false] = 
            Pr[LossyImp_Game(LKG, V, C).main_pk(arg{1}) @ &1 : !res].
+ byequiv => //; conseq (_: ={res}); 1:smt(). 
  by proc;sim. 
have -> : Pr[ExpImp(LKG).epsmax_pk_b(arg{2}) @ &2 : res = false] = 
            Pr[ExpImp(LKG).epsmax_pk_b(arg{2}) @ &2 : !res].
+ byequiv => //; conseq (_: ={res}); 1:smt(). 
  by proc;sim. 
move => *; rewrite Pr[mu_not] HA Pr[mu_not] HB eqarg.
have -> : Pr[LossyImp_Game(LKG, V, C).main_pk(arg{2}) @ &1 : true] = 1%r.
   byphoare => //;proc;inline*. islossless.
have -> : Pr[ExpImp(LKG).epsmax_pk_b(arg{2}) @ &2 : true] = 1%r.
  byphoare => // . proc. inline*. islossless. admit. (*rewrite dbiased_ll.*)
done.
qed.

(* Assumption: epsmax() is bounded by some small epsilon *)


(* the following only holds for LossyPKG that are operator based... *)
require import RealSeries.
require import StdBigop. 
import Bigreal.
import BRA.

lemma fromExpToSum &m  : 
  Pr[ ExpImp(L).epsmax_b() @ &m : res ] =
    big predT (fun (pk: PK) => (mu1 lossy_kg pk) * 
                 max_prob dC
                 (fun (w : W) (c : C) => has (verify pk w c) FinZ.enum) FinW.enum)  FinPK.enum.
proof.
rewrite -sumE_fin; [ by apply FinPK.enum_uniq | by move => *; rewrite FinPK.enumP |].
byphoare => //.
proc; inline *;wp.
rndsem 0; rnd (fun (x : (_*_*_*_*_*_*_)) => x.`7); auto => />.
rewrite dletE; apply eq_sum => pk /=; congr.
rewrite dmapE (mu_eq _ _ (pred1 true)) /(\o) //=; 1: by smt().
by rewrite dbiased1E /= clamp_id //; apply max_prob_bounded; smt(in_nil FinW.enumP).
qed.    
    
(*    
This lemma permits translating any reduction that comes with a term expressed as the expected
value over public keys of the max prob of getting a good challenge into one that talks
about the advantage of an inf theoretical adv against lossy impersonation.
*)      

lemma InfThImpersonation &m  : 
  Pr[ LossyImp_Game (L,V,C).main() @ &m : res ] =
    big predT (fun (pk: PK) => (mu1 lossy_kg pk) * 
                 max_prob dC
                 (fun (w : W) (c : C) => has (verify pk w c) FinZ.enum) FinW.enum)  FinPK.enum
 by rewrite (tight_upper_bound &m L); apply fromExpToSum.

end LossyIDS.
