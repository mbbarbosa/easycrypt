require import AllCore List Distr RealExp FinType.
require T_OW2H.


theory U_Implicit.


type msg.
type pkey.
type skey.
type cph.

(**************************************************************)
(*                                                            *)
(*                   PKE Definitions                          *)
(*                                                            *)
(**************************************************************)

(* Deterministic Encryption and Decryption *)
op enc : pkey -> msg -> cph.
op dec : skey -> cph -> msg option.

op [lossless]kg : (pkey * skey) distr.
op [lossless is_uniform]md : msg distr.

op eps_injective = mu kg (fun (kp : pkey * skey) => !injective (enc kp.`1)).

qmodule type FFC_Adv = {
   proc find(pk : pkey) : cph list 
}.

module FFC(A : FFC_Adv) = {
   proc main() : bool = {
      var kp,l;
      kp <$ kg;
      l <@ A.find(kp.`1);
      return exists c m, c \in l /\ enc kp.`1 m = c /\
                         dec kp.`2 c <> Some m;
   }
}.

qmodule type OWAdv = {
   proc find(pk : pkey, c : cph) : msg
}.

module OW(A : OWAdv)  = {
   proc main() = {
      var m, c, m', kp;
      kp <$ kg;
      m <$ md;
      c <- enc kp.`1 m;
      m' <@ A.find(kp.`1,c);
      return c = enc kp.`1 m';
   }
}.

(**************************************************************)
(*                                                            *)
(*                   PRF Definitions                          *)
(*                                                            *)
(**************************************************************)

type prfk.
type key.

clone import FinType with type t <- key.

op prf : prfk -> cph -> key.

op [lossless]prfkd : prfk distr.

op [lossless]kd : key distr.


(* The real and ideal PRF modules and the PRF game. *)

clone import MUniFinFun as F with
   type t <- cph.

op [lossless]fd = F.dfun (fun _ => kd).

module type F_t = {
   qproc o(x : cph) : key
}.

module type Fi_t = {
   proc init() : unit
   qproc o(x : cph) : key
}.

module PRF : Fi_t = {
   var prfk : prfk
   proc init() = { prfk <$ prfkd; }
   qproc o(x : cph) : key = {
      return prf prfk x;
   }
}.

module RO_F : Fi_t = {
   var f : cph -> key
   proc init() = { f <$ fd; }
   qproc o(x : cph) : key = {
      return f x;
   }
}.

qmodule type PRF_Adv(F : F_t) = {
   proc guess() : bool
}.

module PRF_Security(F : Fi_t, A : PRF_Adv) = {
   proc main() : bool = {
        var b;
        F.init();
        b <@ A(F).guess();
        return b;
   }
}.

(**************************************************************)
(*                                                            *)
(*                   The Random Oracle                        *)
(*                                                            *)
(**************************************************************)

clone import MUniFinFun as H with
   type t <- msg * cph.

op hd = H.dfun (fun _ => kd).

(* The adversary's QROM interface *)
module type H_t = {
   qproc o(x : msg * cph) : key
}.

module type Hi_t = {
   proc init(pk : pkey) : unit (* Type allows pk so that it can be reused throuhout *)
   qproc o(x : msg * cph) : key
   proc o2(x : cph * cph) : key (* Used later in proof *)
}.

module RO_H : Hi_t = {
   var h : msg * cph -> key
   proc init(pk : pkey) = { h <$ hd; } (* pk is ignored; pure QROM *)
   qproc o(x : msg * cph) : key = {
      return h x;
   }
   proc o2(x : cph * cph) : key = { return witness; } (* Used later in proof *)
}.

(**************************************************************)
(*                                                            *)
(*                   The U Transform                          *)
(*                                                            *)
(**************************************************************)

type keypair = pkey * (pkey * skey * prfk).

module Scheme(OH : H_t, OF : F_t) = {
   proc kg() : keypair = {
       var pk, sk, prfk;
       (pk,sk) <$ kg;
       prfk <$ prfkd;
       return (pk,(pk,sk,prfk));
   }
   proc enc(pk : pkey) : key * cph = {
       var m, c,k;
       m <$ md;
       c <- enc pk m;
       k <@ OH.o(m,c);
       return (k, c);
   }

   proc dec(sk' : pkey * skey * prfk, c : cph) : key = {
       var mo, k, pk, sk, prfk;
       (pk, sk, prfk) <- sk';
       mo <- dec sk c;
       if (mo = None \/ enc pk (oget mo) <> c) {
          k <@ OF.o(c); 
       }
       else {
          k <@ OH.o(oget mo,c);
       }
       return k;
   }
}.

(**************************************************************)
(*                                                            *)
(*                   KEM CCA Security                         *)
(*                                                            *)
(**************************************************************)

module type CCAOi_t(H : Hi_t, F : Fi_t) = {
  proc init(b : bool) : pkey * key * cph
  proc dec(c : cph) : key option
}.

module type CCAO_t = {
  proc dec(c : cph) : key option
}.

qmodule type CCAAdv_t(CCAO : CCAO_t, OH : H_t) = {
   proc guess(pk : pkey, k : key, c : cph) : bool
}.


module (CCAO : CCAOi_t) (H : Hi_t, F : F_t) = {
   var _kp : keypair
   var _chal : cph
   var _log : cph list

   proc init(b : bool) : pkey * key * cph = {
      var k0,k1;
      _log <- [];
      _kp <@ Scheme(H,F).kg(); (* Key generation should not use FO oracles *)
      (k0,_chal) <@ Scheme(H,F).enc(_kp.`1);
      k1 <$ kd;
      return (_kp.`1,if b then k1 else k0,_chal);
   }

   proc dec(c : cph) : key option = {
        var k;
        _log <- c :: _log;
        k <@ Scheme(H,F).dec(_kp.`2, c);
        return if (c <> _chal) then Some k else None;
   }

}.

module RealIdeal(OH : Hi_t, OF : Fi_t, OCCA : CCAOi_t, A : CCAAdv_t) = {
   proc main(b : bool) = {
      var chal;
      OF.init();
      OH.init(witness); 
      chal <@ OCCA(OH,OF).init(b);
      b <@ A(OCCA(OH,OF), OH).guess(chal);
      return b;
   }
}.

(**************************************************************)
(*                                                            *)
(*                   Security Proof                           *)
(*                                                            *)
(**************************************************************)


(* Hop 0: PRF Hop *)

section.

declare qmodule A <: CCAAdv_t {-RO_H, -CCAO, -PRF, -RO_F}.

module (D0(OH : Hi_t, A : CCAAdv_t) : PRF_Adv) (OF : F_t)  = {
    proc guess (): bool = {
      var chal,b;
      OH.init(witness);
      chal <@ CCAO(OH,OF).init(false);
      b <@ A(CCAO(OH,OF), OH).guess(chal);
      return b;
    }
}.

module (D1(OH : Hi_t, A : CCAAdv_t) : PRF_Adv) (OF : F_t)  = {
    proc guess (): bool = {
      var chal,b;
      OH.init(witness);
      chal <@ CCAO(OH,OF).init(true);
      b <@ A(CCAO(OH,OF), OH).guess(chal);
      return b;
    }
}.

equiv hop0_00 :
  RealIdeal(RO_H,PRF,CCAO,A).main ~ PRF_Security(PRF, D0(RO_H,A)).main : !b{1} /\ ={glob A}  ==> ={res}.
proc.
inline *; wp;call(_: ={glob RO_H, glob CCAO, glob PRF}). 
+ by sim.
+ by sim.
by auto => />.
qed.

equiv hop0_01 :
  RealIdeal(RO_H,RO_F,CCAO,A).main ~ PRF_Security(RO_F, D0(RO_H,A)).main : !b{1} /\ ={glob A}  ==> ={res}.
proc.
inline *; wp;call(_: ={glob RO_H, glob CCAO, glob RO_F}). 
+ by sim.
+ by sim.
by auto => />.
qed.

equiv hop0_10 :
  RealIdeal(RO_H,PRF,CCAO,A).main ~ PRF_Security(PRF, D1(RO_H,A)).main : b{1} /\ ={glob A}  ==> ={res}.
proc.
inline *; wp;call(_: ={glob RO_H, glob CCAO, glob PRF}). 
+ by sim.
+ by sim.
by auto => />.
qed.

equiv hop0_11 :
  RealIdeal(RO_H,RO_F,CCAO,A).main ~ PRF_Security(RO_F, D1(RO_H,A)).main : b{1} /\ ={glob A}  ==> ={res}.
proc.
inline *; wp;call(_: ={glob RO_H, glob CCAO, glob RO_F}). 
+ by sim.
+ by sim.
by auto => />.
qed.

lemma hop00_pr &m  :
   Pr[ RealIdeal(RO_H, PRF, CCAO, A).main(false) @ &m : res ] -
      Pr[ RealIdeal(RO_H, RO_F, CCAO, A).main(false) @ &m : res ]=
        Pr[PRF_Security(PRF, D0(RO_H, A)).main()  @ &m : res ] - 
           Pr[PRF_Security(RO_F, D0(RO_H, A)).main()  @ &m : res ].
+ have -> : Pr[ RealIdeal(RO_H, PRF, CCAO, A).main(false) @ &m : res ] =
             Pr[PRF_Security(PRF, D0(RO_H, A)).main()  @ &m : res ] by byequiv (hop0_00). 
  by have -> : Pr[ RealIdeal(RO_H, RO_F, CCAO, A).main(false) @ &m : res ] =
             Pr[PRF_Security(RO_F, D0(RO_H, A)).main()  @ &m : res ] by byequiv (hop0_01). 
qed. 

lemma hop01_pr &m :
   Pr[ RealIdeal(RO_H, PRF, CCAO, A).main(true) @ &m : res ] -
      Pr[ RealIdeal(RO_H, RO_F, CCAO, A).main(true) @ &m : res ]=
        Pr[PRF_Security(PRF, D1(RO_H, A)).main()  @ &m : res ] - 
           Pr[PRF_Security(RO_F, D1(RO_H, A)).main()  @ &m : res ].
+ have -> : Pr[ RealIdeal(RO_H, PRF, CCAO, A).main(true) @ &m : res ] =
             Pr[PRF_Security(PRF, D1(RO_H, A)).main()  @ &m : res ] by byequiv (hop0_10). 
  by have -> : Pr[ RealIdeal(RO_H, RO_F, CCAO, A).main(true) @ &m : res ] =
             Pr[PRF_Security(RO_F, D1(RO_H, A)).main()  @ &m : res ] by byequiv (hop0_11).
qed. 


end section.

(* Hop 1: Change RO_G to use F(enc m,c). *)

clone import MUniFinFun as H1 with
   type t <- cph * cph.

op dhc = H1.dfun (fun _ => kd). 

op hd1(pk : pkey) : ((msg * cph) -> key) distr = 
  dmap dhc (fun h => ((fun (mc : (msg * cph)) => h (enc pk mc.`1, mc.`2)))).

lemma inj_cancel ['a 'b] (f : 'a -> 'b) :
      injective f => exists f', cancel f f'.
pose P y := fun x => f x = y.
pose g y := choiceb (P y) witness.
move=> inj_f; exists g => x; apply: inj_f => @/g.
by rewrite (choicebP (P (f x)) witness) //; exists x.
qed.


import StdBigop.Bigreal.

(* We factor out the proof that the distributions of the
   sampled functions are the same *)
lemma equal_distr pk : injective (enc pk) => hd1 pk = hd.
move => enc_inj.
rewrite /hd1 /hd eq_distr => h.
rewrite dmap1E /dhc /= /pred1 /(\o) /=.
pose p1 := fun (cc: cph * cph) k =>
   (exists m, enc pk m = cc.`1 /\ k = h (m, cc.`2)) \/
   (forall m, enc pk m <> cc.`1).
have -> : 
  (fun (x : cph * cph -> key) => (fun (mc0 : msg * cph) => x (enc pk mc0.`1, mc0.`2)) = h) =
   fun (f : cph * cph -> key) => forall cc, p1 cc (f cc).
by apply fun_ext => f /=; rewrite /p1 /= eq_iff /#. 
pose p := fun (mc : msg * cph) k => h mc = k. 
have -> : (transpose (=) h = fun (f : msg * cph -> key) => forall mc, p mc (f mc)).
by apply fun_ext => f /=;rewrite /p /= fun_ext /#.
rewrite H1.dfunE H.dfunE /=.
pose piq(cc : (_*cph)) := forall (m : msg), enc pk m <> cc.`1.
rewrite (BRM.bigID _ _ piq)  !predTI /=.
have -> /= : BRM.big piq (fun (x : cph * cph) => mu kd (p1 x)) FinT.enum = 1%r.
rewrite -(BRM.eq_bigr _ (fun _ => 1%r)) /=.
+ rewrite /p1 /piq /= => i H. 
  by smt(kd_ll  mu_eq).
by apply BRM.big1.
elim (inj_cancel _ enc_inj) => f' Hf.
pose ff(cc : cph * cph) := (f' cc.`1,cc.`2).
pose ff'(mc : msg * cph) := (enc pk mc.`1, mc.`2).
have cncl : cancel ff' ff by smt().
rewrite -BRM.big_filter.
rewrite (BRM.big_reindex _ _ ff' ff _ _) /(\o) /=. 
+ by move => cc; rewrite /predC /= /ff' /ff /=; smt(enumP mem_filter). 
rewrite /predT /=.
have -> : (fun (x : msg * cph) => mu kd (p1 (ff' x))) = (fun (x : msg * cph) => mu kd (p x)).
+ rewrite fun_ext => cc; congr. 
  by rewrite /p1 /p /ff' /= fun_ext => k; smt().
apply BRM.eq_big_perm.
search (_ => perm_eq _ _).
apply uniq_perm_eq. 
+ rewrite -pmap_some;apply pmap_inj_in_uniq. 
  + by move => cc1 cc2 mc; rewrite !mem_filter /predC /= => Hcc1 Hcc2 /= /#.
  by apply filter_uniq; rewrite FinT.enum_uniq /=.
+ by apply H.FinT.enum_uniq.
move => mc; rewrite H.FinT.enumP /=. 
have -> : (mc = ff (ff' mc)) by smt().
by rewrite map_f mem_filter /= FinT.enumP /= /#. 
qed.

module RO_H1 : Hi_t = {
   var hc : cph * cph -> key
   include RO_H [-init,o2]
   proc init(pk : pkey) = { 
        hc <$ dhc; 
        RO_H.h <- fun (mc : (msg * cph)) => hc (enc pk mc.`1, mc.`2); 
   }
   proc o2(cc : cph * cph) : key = { return hc cc; } (* used only in next hop *)
}.

module RealIdeal1(OH : Hi_t, OF : Fi_t, OCCA : CCAOi_t, A : CCAAdv_t) = {
   proc main(b : bool) = {
      var chal,k0,k1;
      OF.init();
      CCAO._log <- [];
      CCAO._kp <@ Scheme(OH,OF).kg();
      if (injective (enc CCAO._kp.`1)) {
         OH.init(CCAO._kp.`1);
         (k0,CCAO._chal) <@ Scheme(OH,OF).enc(CCAO._kp.`1);
         k1 <$ kd;
         chal <- (CCAO._kp.`1,if b then k1 else k0,CCAO._chal);
         b <@ A(OCCA(OH,OF), OH).guess(chal);
      }
      return b /\ injective (enc CCAO._kp.`1);
   }
}.

(* The proof is then an up to bad argument on the probability of 
   sampling a bad PK. For that we redefine the security game such that
   nothing happens if the bad event occurs *)

section.

declare module A <: CCAAdv_t {-CCAO, -RO_H1, -RO_F}.

lemma hop1_notbad :
 (forall (CCAO0 <: CCAO_t) (OH <: H_t),
 islossless OH.o => 
 islossless CCAO0.dec => islossless A(CCAO0, OH).guess) =>
  equiv [
  RealIdeal(RO_H,RO_F,CCAO,A).main ~ RealIdeal1(RO_H1, RO_F,CCAO,A).main : ={b, glob A} 
                 ==> (!injective (enc CCAO._kp{1}.`1) <=> !injective (enc CCAO._kp{2}.`1)) /\
                     ((injective (enc CCAO._kp{2}.`1) => ={res}))].
move => A_guess_ll.
proc.
inline {1} 3; inline {1} 5; inline {2} 3.
swap {1} 3 -2. swap {1} [4..7] -1;sp.
seq 5 5 : (#pre /\ ={glob RO_F, CCAO._kp, CCAO._log}); 1: by inline *; auto => />.
sp; if{2}; last first. 
+ inline *;wp;call {1} (_: true ==> true).
  + by apply (A_guess_ll (CCAO(RO_H, RO_F)) (RO_H)); islossless. 
  by auto => />;smt(H.dfun_ll kd_ll).
call(_: !(injective (enc CCAO._kp.`1)),
        ={glob RO_H, glob RO_F, glob CCAO},
        (!injective (enc CCAO._kp{1}.`1) <=> !injective (enc CCAO._kp{2}.`1)) /\
        (injective (enc CCAO._kp{2}.`1) => ={CCAO._kp,CCAO._kp})).
+ by move => CCAO0 OH; apply (A_guess_ll CCAO0 OH).
+ by conseq => />;sim. 
+ by move => *; conseq />; islossless. 
+ by move => *; conseq />; islossless. 
+ by conseq => />;sim. 
+ by move => *; conseq />; islossless. 
+ by move => *; conseq />; islossless. 
inline {1} 2; inline {2} 2; inline {1} 5; inline {2} 5; auto => />; 1: smt().
call (_: injective (enc CCAO._kp{2}.`1) /\  arg{2} = CCAO._kp{2}.`1  ==> injective (enc CCAO._kp{2}.`1) => ={RO_H.h}).
+ bypr (RO_H.h{1}) (RO_H.h{2}) => // &1 &2 a enc_inj.
  have -> : Pr[RO_H.init(arg{1}) @ &1 : RO_H.h = a] = mu1 hd a.
  + by byphoare => //; proc; rnd; skip => />.
  have -> : Pr[RO_H1.init(arg{2}) @ &2 : RO_H.h = a] = mu1 (hd1 arg{2}) a.
  + byphoare (_: pk = arg{2} ==> _) => //; proc; wp; rnd; skip => />.
    by rewrite /hd1 /= dmap1E.
  by rewrite (equal_distr _  _); smt().
by auto => />.
qed.

lemma hop1_notbad_pr &m b : 
 (forall (CCAO0 <: CCAO_t) (OH <: H_t),
 islossless OH.o => 
 islossless CCAO0.dec => islossless A(CCAO0, OH).guess) =>
  `| Pr[RealIdeal(RO_H, RO_F, CCAO, A).main(b) @ &m : res] -
     Pr[RealIdeal1(RO_H1, RO_F, CCAO,A).main(b) @ &m : res] | <= 
       Pr[RealIdeal1(RO_H1, RO_F, CCAO, A).main(b) @ &m : ! injective (enc CCAO._kp.`1)]
 by move => A_ll;byequiv (hop1_notbad A_ll) : (! injective (enc CCAO._kp.`1)) => //= /#.

lemma hop1_bad_pr &m b :
 (forall (CCAO0 <: CCAO_t) (OH <: H_t),
 islossless OH.o => 
 islossless CCAO0.dec => islossless A(CCAO0, OH).guess) =>
   Pr[ RealIdeal1(RO_H1, RO_F,CCAO, A).main(b) @ &m : !injective (enc CCAO._kp.`1) ] = eps_injective.
move => A_ll.
byphoare => //.
proc;inline *. 
swap 3 1; seq 5 :  (! injective (enc CCAO._kp.`1)) (eps_injective)  (1%r) (1%r - eps_injective) (0%r) => //=.
+ wp; rnd (fun (kp : _*_) => ! injective (enc kp.`1)); 
     auto => />; smt(fd_ll prfkd_ll).
+ conseq />;islossless.
  + by apply (A_ll (CCAO(RO_H1,RO_F)) (RO_H1)); islossless. 
  by rewrite /dhc; smt(dfun_ll kd_ll).
hoare; inline *;sp;if.
+ by auto => />. 
by auto => />. 
qed.


end section.

(* Hop 2: Use F directly in Decaps; not much is happening here,
   since we were already hashing using F *)

module (CCAO2 : CCAOi_t) (OH : Hi_t, OF : F_t) = {
   include CCAO(OH,OF) [-dec]

   proc dec(c : cph) : key option = {
       var mo, k;
       CCAO._log <- c :: CCAO._log;
       mo <- dec CCAO._kp.`2.`2 c;
       if (mo = None \/ enc CCAO._kp.`1 (oget mo) <> c) {
          k <@ OF.o{c};
       }
       else {
          k <@ OH.o2((c,c));
       }
        return if (c <> CCAO._chal) then Some k else None;
   }

}.

equiv hop2 (A <: CCAAdv_t {-CCAO2, -RO_H1, -RO_F}) :
  RealIdeal1(RO_H1,RO_F,CCAO,A).main ~ RealIdeal1(RO_H1,RO_F,CCAO2,A).main : ={b, glob A} ==> ={res}.
proc.
seq 3 3 : (#pre /\ ={glob RO_F, CCAO._kp, CCAO._log} /\ CCAO._kp{2}.`2.`1 = CCAO._kp{2}.`1); 1: by inline *;auto => />.
if => //.
call(_: ={glob RO_H, glob CCAO, glob RO_F} /\ 
         CCAO._kp{1}.`2.`1 = CCAO._kp{1}.`1 /\
         (forall m c, RO_H.h{1} (m,c) = RO_H1.hc{2} (enc CCAO._kp{1}.`1 m, c))).
+ by conseq => />; sim.
+ by proc; inline *; conseq />; auto => /> /#. 
inline *;  auto => />.
qed.

lemma hop2_pr (A <: CCAAdv_t {-CCAO2, -RO_H1, -RO_F}) &m b:
  Pr[RealIdeal1(RO_H1, RO_F, CCAO, A).main(b) @ &m : res] =
  Pr[RealIdeal1(RO_H1, RO_F, CCAO2, A).main(b) @ &m : res]
  by byequiv (hop2 A) => //.

(* Hop 3: Use only F in Decaps. This implies merging two random functions
   arguing that throughout the game they are always queried on disjoint
   sets of inputs.  *)

module (CCAO3 : CCAOi_t) (OH : Hi_t, OF : F_t) = {
   include CCAO2(OH,OF) [-dec]

   proc dec(c : cph) : key option = {
       var k;
       CCAO._log <- c :: CCAO._log;
       k <@ OH.o2(c,c);
       return if (c <> CCAO._chal) then Some k else None;
   }

}.


section.

declare module A <: CCAAdv_t {-CCAO3, -RO_H1, -RO_F}.

module Bridge = {
   var hc0 : cph * cph -> key
   var f : cph -> key
   var hc : cph * cph -> key

   proc bL(pk : pkey, sk : skey) = {
      f <$ fd;
      hc0 <$ dhc;
      hc <-
  fun (cc : cph * cph) =>
    if cc.`1 <> cc.`2 then hc0 cc
    else
      if dec sk cc.`1 = None \/ enc pk (oget (dec sk cc.`1)) <> cc.`1 then
        if exists (m0 : msg), enc pk m0 = cc.`1 /\ dec sk cc.`1 <> Some m0 then
          hc0 cc
        else f cc.`1
      else hc0 cc;
   }

   proc bR() = {
     hc <$ dhc;
   }
}.

equiv bridge pk sk : Bridge.bL ~ Bridge.bR : arg{1} = (pk,sk) ==> ={Bridge.hc}.
proof.
proc.
rnd : *0 *0; auto => />.
have -> : dmap dhc (fun (hc : cph * cph -> key) => hc)  = 
  (dlet fd
        (fun (f : cph -> key) =>
           dmap dhc
             (fun (hc0 : cph * cph -> key) (cc : cph * cph) =>
                if cc.`1 <> cc.`2 then hc0 cc
                else
                  if dec sk cc.`1 = None \/ enc pk (oget (dec sk cc.`1)) <> cc.`1 then
                    if exists (m0 : msg), enc pk m0 = cc.`1 /\ dec sk cc.`1 <> Some m0 then hc0 cc else f cc.`1
                  else hc0 cc))); last by done.
rewrite /dhc  /fd dmap_id /=.
search dlet dfun.
admitted.

lemma hop3_notbad :
 (forall (CCAO0 <: CCAO_t) (OH <: H_t),
 islossless OH.o => 
 islossless CCAO0.dec => islossless A(CCAO0, OH).guess) =>
equiv[
  RealIdeal1(RO_H1,RO_F,CCAO2,A).main ~ RealIdeal1(RO_H1,RO_F,CCAO3,A).main : ={b, glob A} ==> 
   let bad1 = (exists (m : msg) (c : cph), enc CCAO._kp{1}.`1 m = c /\ 
                                  c \in CCAO._log{1} /\ 
                                  dec CCAO._kp{1}.`2.`2 c <> Some m) in
   let bad2 = (exists (m : msg) (c : cph), enc CCAO._kp{2}.`1 m = c /\ 
                                  c \in CCAO._log{2} /\ 
                                  dec CCAO._kp{2}.`2.`2 c <> Some m) in
              (bad1 <=> bad2) /\ (!bad2 => ={res})].
move => A_guess_ll.
proc.
swap {1} 1 2.
seq 2 3 : (#pre /\ ={CCAO._kp, CCAO._log} /\ CCAO._kp{2}.`2.`1 = CCAO._kp{2}.`1); 1: by inline *;auto => />.
inline *; if {2}; 2: by rcondf {1} 2; by move => *; auto.
rcondt{1} 2; first by move => *; auto => />.
call(_: 
     exists m c, enc CCAO._kp.`1 m = c /\ c \in CCAO._log /\ dec CCAO._kp.`2.`2 c <> Some m,
     ={glob RO_H, glob CCAO, CCAO._log} /\ 
          RO_H1.hc{2} = fun (cc : _*_) =>
               if ((cc.`1 <> cc.`2))
               then RO_H1.hc{1} cc
               else let  mo = dec CCAO._kp{2}.`2.`2 cc.`1 in 
                    if (mo = None \/ enc CCAO._kp{2}.`1 (oget mo) <> cc.`1) 
                    then if (exists m, enc CCAO._kp{2}.`1 m = cc.`1 /\ 
                                      dec CCAO._kp{2}.`2.`2 cc.`1 <> Some m)
                         then RO_H1.hc{1} cc
                         else RO_F.f{1} cc.`1
                    else RO_H1.hc{1} cc,
     let bad1 = (exists (m : msg) (c : cph), enc CCAO._kp{1}.`1 m = c /\ 
                                  c \in CCAO._log{1} /\ 
                                  dec CCAO._kp{1}.`2.`2 c <> Some m) in
     let bad2 = (exists (m : msg) (c : cph), enc CCAO._kp{2}.`1 m = c /\ 
                                  c \in CCAO._log{2} /\ 
                                  dec CCAO._kp{2}.`2.`2 c <> Some m) in
              (bad1 <=> bad2) /\ (={CCAO._kp})).
+ by move => CCAO OH; apply (A_guess_ll CCAO OH).
+ by sim />.
+ by move => *; conseq />; islossless. 
+ by move => *; conseq />; islossless.
+ by proc; inline *; auto => /> /#.
+ move => &2 bad; proc; inline *; auto => /> /#.  
+ by move => *; conseq />; proc; inline *; auto => /> /#. 
inline *; swap {1} 2 -1;sp;wp.
rnd;wp;rnd;wp.
conseq (_: _ ==>
       RO_H1.hc{2} =
   fun (cc : cph * cph) =>
     if cc.`1 <> cc.`2 then RO_H1.hc{1} cc
     else
       if dec CCAO._kp{2}.`2.`2 cc.`1 = None \/ enc CCAO._kp{2}.`1 (oget (dec CCAO._kp{2}.`2.`2 cc.`1)) <> cc.`1 then
         if exists (m0 : msg), enc CCAO._kp{2}.`1 m0 = cc.`1 /\ dec CCAO._kp{2}.`2.`2 cc.`1 <> Some m0 then
           RO_H1.hc{1} cc
         else RO_F.f{1} cc.`1
       else RO_H1.hc{1} cc); 1: smt().
  transitivity {1} { Bridge.bL(CCAO._kp.`1,CCAO._kp.`2.`2); } 
     (={CCAO._kp} ==> ={CCAO._kp} /\ RO_H1.hc{1} = Bridge.hc0{2} /\ RO_F.f{1} = Bridge.f{2} /\
       Bridge.hc{2} = fun (cc : cph * cph) =>
    if cc.`1 <> cc.`2 then Bridge.hc0{2} cc
    else
      if dec CCAO._kp{1}.`2.`2 cc.`1 = None \/ enc CCAO._kp{1}.`1 (oget (dec CCAO._kp{1}.`2.`2 cc.`1)) <> cc.`1 then
        if exists (m0 : msg), enc CCAO._kp{1}.`1 m0 = cc.`1 /\ dec CCAO._kp{1}.`2.`2 cc.`1 <> Some m0 then
          Bridge.hc0{2} cc
        else Bridge.f{2} cc.`1
      else Bridge.hc0{2} cc)
     ( ={CCAO._kp} ==> ={CCAO._kp} /\ RO_H1.hc{2} = Bridge.hc{1}); 1,2: smt(). 
  + by inline *; auto => />.
  transitivity {2} { Bridge.bR(); } 
     ( ={CCAO._kp} ==> ={CCAO._kp} /\ ={Bridge.hc}) 
     ( ={CCAO._kp} ==> ={CCAO._kp}  /\ Bridge.hc{1} = RO_H1.hc{2} ) ; 1,2:  smt(). 
   conseq />; ecall (bridge CCAO._kp{2}.`1 CCAO._kp{2}.`2.`2); auto => />. 
  + by inline *; auto => />.
qed.

module B0(A : CCAAdv_t)  : FFC_Adv = {
   proc find(pk : pkey) : cph list = {
      var k0, k1, chal, b;
      RO_F.init();
      CCAO._log <- [];
      CCAO._kp <- (pk,(pk,witness,witness));
      if (injective (enc CCAO._kp.`1)) {
         RO_H1.init(CCAO._kp.`1);
         (k0,CCAO._chal) <@ Scheme(RO_H1,RO_F).enc(CCAO._kp.`1);
         k1 <$ kd;
         chal <- (CCAO._kp.`1, k0,CCAO._chal);
         b <@ A(CCAO3(RO_H1,RO_F), RO_H1).guess(chal);
      }
      return CCAO._log;
  }
}.

equiv hop3_bad0 :
   FFC(B0(A)).main ~ RealIdeal1(RO_H1,RO_F,CCAO3,A).main : b{2} = false /\ ={glob A} ==> 
   (exists (m : msg) (c : cph), enc CCAO._kp{2}.`1 m = c /\ 
                                  c \in CCAO._log{2} /\ 
                                  dec CCAO._kp{2}.`2.`2 c <> Some m) => res{1}.
proc.
inline *;wp; swap {1} 3 -2.
seq 5 5 : (#pre /\ ={CCAO._log} /\ 
           CCAO._kp{1}.`1 = CCAO._kp{2}.`1 /\ 
           CCAO._kp{2}.`1 = CCAO._kp{2}.`2.`1 /\ 
           CCAO._kp{2}.`2.`2 = kp{1}.`2 /\
           CCAO._kp{2}.`2.`1 = kp{1}.`1 /\
           CCAO._log{1} = []); 1: by wp;rnd{2};auto => />.
if; [ by  smt() | | by auto => /> /# ]. 
call (_: ={glob RO_H1, CCAO._chal,CCAO._log} /\
       CCAO._kp{1}.`1 = CCAO._kp{2}.`1 /\ 
       CCAO._kp{2}.`2.`1 = CCAO._kp{2}.`1 ).
+ by conseq />;sim.
+ by conseq />;sim.
by auto => /> /#. 
qed.

module B1(A : CCAAdv_t)  : FFC_Adv = {
   proc find(pk : pkey) : cph list = {
      var k0, k1, chal, b;
      RO_F.init();
      CCAO._log <- [];
      CCAO._kp <- (pk,(pk,witness,witness));
      if (injective (enc CCAO._kp.`1)) {
         RO_H1.init(CCAO._kp.`1);
         (k0,CCAO._chal) <@ Scheme(RO_H1,RO_F).enc(CCAO._kp.`1);
         k1 <$ kd;
         chal <- (CCAO._kp.`1, k1,CCAO._chal);
         b <@ A(CCAO3(RO_H1,RO_F), RO_H1).guess(chal);
      }
      return CCAO._log;
  }
}.

equiv hop3_bad1 :
   FFC(B1(A)).main ~ RealIdeal1(RO_H1,RO_F,CCAO3,A).main : b{2} = true /\ ={glob A} ==> 
   (exists (m : msg) (c : cph), enc CCAO._kp{2}.`1 m = c /\ 
                                  c \in CCAO._log{2} /\ 
                                  dec CCAO._kp{2}.`2.`2 c <> Some m) => res{1}.
proc.
inline *;wp; swap {1} 3 -2.
seq 5 5 : (#pre /\ ={CCAO._log} /\ 
           CCAO._kp{1}.`1 = CCAO._kp{2}.`1 /\ 
           CCAO._kp{2}.`1 = CCAO._kp{2}.`2.`1 /\ 
           CCAO._kp{2}.`2.`2 = kp{1}.`2 /\
           CCAO._kp{2}.`2.`1 = kp{1}.`1 /\
           CCAO._log{1} = []); 1: by wp;rnd{2};auto => />.
if; [ by  smt() | | by auto => /> /# ]. 
call (_: ={glob RO_H1, CCAO._chal,CCAO._log} /\
       CCAO._kp{1}.`1 = CCAO._kp{2}.`1 /\ 
       CCAO._kp{2}.`2.`1 = CCAO._kp{2}.`1 ).
+ by conseq />;sim.
+ by conseq />;sim.
by auto => /> /#. 
qed.

lemma bad30_pr &m : 
  Pr[RealIdeal1(RO_H1, RO_F, CCAO3, A).main(false) @ &m : 
       (exists (m : msg) (c : cph),
          enc CCAO._kp.`1 m = c /\ (c \in CCAO._log) /\ dec CCAO._kp.`2.`2 c <> Some m)] <=
             Pr[FFC(B0(A)).main() @ &m : res ]
  by byequiv => //; symmetry; conseq (hop3_bad0). 

lemma bad31_pr &m : 
  Pr[RealIdeal1(RO_H1, RO_F, CCAO3, A).main(true) @ &m : 
       (exists (m : msg) (c : cph),
         enc CCAO._kp.`1 m = c /\ (c \in CCAO._log) /\ dec CCAO._kp.`2.`2 c <> Some m)] <=
            Pr[FFC(B1(A)).main() @ &m : res ]
  by byequiv => //; symmetry; conseq (hop3_bad1). 

lemma notbad3_pr &m  b:
 (forall (CCAO0 <: CCAO_t) (OH <: H_t),
 islossless OH.o => 
 islossless CCAO0.dec => islossless A(CCAO0, OH).guess) =>
   `| Pr[RealIdeal1(RO_H1, RO_F, CCAO2, A).main(b) @ &m : res ] -
       Pr[RealIdeal1(RO_H1, RO_F, CCAO3, A).main(b) @ &m : res] | <=
        Pr[RealIdeal1(RO_H1, RO_F, CCAO3, A).main(b) @ &m : 
             (exists (m : msg) (c : cph),
             enc CCAO._kp.`1 m = c /\ (c \in CCAO._log) /\ dec CCAO._kp.`2.`2 c <> Some m)]
 by move => A_ll;byequiv (hop3_notbad A_ll) : 
     (exists (m : msg) (c : cph),  enc CCAO._kp.`1 m = c /\ 
             (c \in CCAO._log) /\ dec CCAO._kp.`2.`2 c <> Some m) => //= /#.
end section.


(* Reusable randomness sampling bridge *)

module Bridge = {
   var hc0 : cph * cph -> key
   var kl : key
   var hc : cph * cph -> key

   proc bL(c : cph) = {
      hc0 <$ dhc;
      kl <$ kd;
      hc <- (fun (cc : cph * cph) => if cc.`1 = c /\ cc.`1 = cc.`2 then kl else hc0 cc);
   }

   proc bR() = {
     hc <$ dhc;
   }
}.

equiv bridge c : Bridge.bL ~ Bridge.bR : arg{1} = c ==> ={Bridge.hc}.
proof.
proc.
rnd : *0 *0.
auto => />.
have -> : (dmap dhc (fun (hc : cph * cph -> key) => hc)) =
          (dlet dhc
        (fun (hc0 : cph * cph -> key) =>
           dmap kd (fun (kl : key) (cc : cph * cph) => if cc.`1 = c /\ cc.`1 = cc.`2 then kl else hc0 cc)));last by done.
rewrite /dhc. 
have /=  H:= dlet_dfun_update (fun (_ : cph * cph) => kd) (c,c);rewrite /("_.[_<-_]") /=. 
have -> : dlet (dfun (fun (_ : cph * cph) => kd))
  (fun (hc0 : cph * cph -> key) =>
     dmap kd (fun (kl : key) (cc : cph * cph) => if cc.`1 = c /\ cc.`1 = cc.`2 then kl else hc0 cc)) = 
     (weight kd \cdot dfun (fun (_ : cph * cph) => kd)).
+ by rewrite -H;congr; rewrite fun_ext => x; congr;smt().
rewrite kd_ll /= dscalar1 /=. 
by rewrite dmap_id.
qed.

(* Now decryption does not use the secret key, so we can reduce to one wayness.
   However, before we do that we must remove the challenge randomness from the
   random oracle. We give two bounds, which have essentially the same proofs,
   one using the semi-classical theorem, and the other using the two-sided
   theorem *)


theory SemiClassicalBound.


(* Note that we need a quite complex random function to match what
   happens in the game. Indeed, decapsulation is using F, while the
   challenge oracle and the adversary are using h built out of F, but
   we need access to both to simulate the game. We therefore model
   this as a random oracle that can be used to compute either h
   or f (we just allow a parallel query) and then rewrite the game
   to use this. The puncturing on a single point is then done by
   using the singleton { (m, enc m), (enc m, enc m)) }. Note that
   this is only a singleton if encryption is injective, which is
   why we need the relaxed version of the two-sided theorem  *)

clone import T_OW2H as SCOW2H with
  type X <- (msg * cph) * (cph * cph),
  type Y <- key * key,
  type Z <- pkey * key * cph,
  type W <- bool.  
import SemiClassical.

module I : Init = {
  proc prm() : ((msg * cph) * (cph * cph) -> key * key) * 
               ((msg * cph) * (cph * cph) -> key * key) * 
               ((msg * cph) * (cph * cph) -> bool) * 
               (pkey * key * cph) * (bool -> bool) = {
     var pk, sk, m,c, h, hc,kleft, kright;
     (pk,sk) <$ kg;
     m <$ md;
     c <- enc pk m;
     hc <$ dhc;
     kleft <$ kd; 
     hc <- fun (cc : _*_) => if cc.`1 = c /\ cc.`1 = cc.`2
                            then kleft 
                            else hc cc;
     h <- fun (mc : (msg * cph)) => hc (enc pk mc.`1, mc.`2);
     kright <$ kd;     
     return (fun (x : (msg * cph) * (cph * cph)) => (h x.`1, hc x.`2), 
             fun (x : (msg * cph) * (cph * cph)) => (kright, kright), 
             fun (x : (msg * cph) * (cph * cph)) => enc pk x.`1.`1 = c /\ 
                                                    x.`1.`2 = c /\ 
                                                    x.`2 = (c,c), 
                          (pk, kleft, c), fun b => b);
  }
}.

module HWrap(O : G_t) = {
     proc init(pk : pkey) = {}
     quantum proc o () {x : msg * cph}: key = {
         quantum var y;
         y <@ O.o{(x,(x.`2,x.`2))};
         return y.`1;
     }
     proc o2 (x : cph * cph): key = {
         var y;
         y <@ O.o{witness,x};
         return y.`2;
     }
}.

module (Awrap(A : CCAAdv_t) : A_t) (O : G_t)  = {
    
   proc run(z : pkey * key * cph) = {
      var pk, kleft,c, k1, b;
      b <- false;
      (pk, kleft, c) <- z;
      RO_F.init();
      CCAO._log <- [];
      CCAO._kp <- (pk,(pk,witness,witness));
      if (injective (enc CCAO._kp.`1)) {
         CCAO._chal <-  c;
         k1 <$ kd;
         b <@ A(CCAO3(HWrap(O),RO_F), HWrap(O)).guess(CCAO._kp.`1,kleft,c);
      }
      return b /\ injective (enc CCAO._kp.`1);
   }
}.

module OWReduction(B : B_t, A : CCAAdv_t) : OWAdv  = {
  var g : (msg * cph) * (cph * cph) -> key * key
  var rep : (msg * cph) * (cph * cph) -> key * key
  var inS  :  (msg * cph) * (cph * cph) -> bool

  (* This procedure is not efficient, but it is just
     preparing the random oracles, so they need to be
     replaced with efficient versions. This should  
     be OK. Apart from that, reduction just uses B. *)
  proc prm(pk : pkey, c : cph) : 
     ((msg * cph) * (cph * cph) -> key * key) * 
               ((msg * cph) * (cph * cph) -> key * key) * 
               ((msg * cph) * (cph * cph) -> bool) * 
               (pkey * key * cph)  = {
     var hc,h, kleft,kright;

     hc <$ dhc;
     kleft <$ kd; 
     hc <- fun (cc : _*_) => if cc.`1 = c /\ cc.`1 = cc.`2
                            then kleft 
                            else hc cc;
     h <- fun (mc : (msg * cph)) => hc (enc pk mc.`1, mc.`2);
     kright <$ kd;     
     return (fun (x : (msg * cph) * (cph * cph)) => (h x.`1, hc x.`2), 
             fun (x : (msg * cph) * (cph * cph)) => (kright, kright), 
             fun (x : (msg * cph) * (cph * cph)) => enc pk x.`1.`1 = c /\ 
                                                    x.`1.`2 = c /\ 
                                                    x.`2 = (c,c), 
                          (pk, kleft, c));
  }

  module O : G_t = {
    quantum proc o{x :  (msg * cph) * (cph * cph)} = { 
       return if inS x then rep x else g x; }
  }

  proc find(pk : pkey, c : cph) = {
      var z,mc;
      (g,rep,inS,z) <@ prm(pk,c);
      mc <@ B(O,Awrap(A)).find(z);
      return mc.`1.`1;
  }
}.


section.

declare module A <: CCAAdv_t {-CCAO,  -G, -RO_F, -RO_H, -RO_H1, -H,  -OWReduction, -PRF, -I}.



lemma left_hop &m :
(forall (O <: CCAO_t) (H <: H_t), islossless H.o => islossless O.dec => islossless A(O,H).guess) =>
  Pr [ A_O(Awrap(A),G(I)).main() @ &m : res]  =
  Pr[RealIdeal1(RO_H1, RO_F, CCAO3, A).main(false) @ &m : res].
 proof. 
move => A_ll.
 byequiv => //.
 proc; inline*;wp.
 swap {2} 4 -3; seq 0 1 : #pre; 1: by auto.
 swap{1} [14..15] -13. 
 seq 3 3 : (#pre /\ ={CCAO._log,sk} /\ pk0{1} = pk{2}); 1: by auto.
 sp; if{2}; last first.
 + rcondf {1} 14; 1: by move => *; auto => />.
   by auto => />; smt(H1.dfun_ll kd_ll). 
 rcondt {1} 14; 1: by move => *; auto => />.
 swap {2} 5 -3; swap {2} 5 -3; sp; seq 1 1 : (#pre /\ ={m}); 1: by auto.
 call(_: ={CCAO._chal} /\ 
          CCAO._kp{1}.`1 = CCAO._kp{2}.`1 /\ 
          G.g{1} = fun (x : (msg * cph) * (cph * cph)) => (RO_H.h{2} x.`1, RO_H1.hc{2} x.`2)).
 + by proc; inline *;auto => />.
 + by proc; inline *;auto => />.
 wp;rnd;wp;rnd{1}; wp;sp.
 conseq (_:  (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 
                                      then kleft0{1} 
                                      else hc{1} cc) = RO_H1.hc{2}); 1: smt().
  transitivity {1} { Bridge.bL(enc pk m); } 
     (true ==> hc{1} = Bridge.hc0{2} /\ kleft0{1} = Bridge.kl{2} /\
       Bridge.hc{2} =  (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 then Bridge.kl{2} else Bridge.hc0{2} cc))
     ( ={pk,m} ==> ={pk,m} /\ RO_H1.hc{2} = Bridge.hc{1}); 1,2: smt(). 
  + by inline *; auto => />.
  transitivity {2} { Bridge.bR(); } 
     ( ={pk,m} ==> ={pk,m}  /\ ={Bridge.hc}) 
     (={pk,m} ==> ={pk,m}  /\ Bridge.hc{1} = RO_H1.hc{2} ) ; 1,2:  smt(). 
   conseq />; ecall (bridge (enc pk{2} m{2})); auto => />. 
  + by inline *; auto => />.
qed.

lemma right_hop  &m :
  Pr [ A_O(Awrap(A),H(I)).main() @ &m : res]  =
  Pr [ RealIdeal1(RO_H1,RO_F,CCAO3,A).main(true) @ &m : res].
 proof. 
 byequiv => //.
 proc; inline*;wp.
 swap {2} 4 -3; seq 0 1 : #pre; 1: by auto.
 swap{1} [14..15] -13. 
 seq 3 3 : (#pre /\ ={CCAO._log,sk} /\ pk0{1} = pk{2}); 1: by auto.
 sp; if{2}; last first.
 + rcondf {1} 14; 1: by move => *; auto => />.
   by auto => />; smt(H1.dfun_ll kd_ll). 
 rcondt {1} 14; 1: by move => *; auto => />.
 swap {2} 5 -3; swap {2} 5 -3; sp; seq 1 1 : (#pre /\ ={m}); 1: by auto.
 call(_: ={CCAO._chal} /\ CCAO._kp{1}.`1 = CCAO._kp{2}.`1 /\ 
     G.inS{1} = (fun (x : (msg * cph) * (cph * cph)) => 
                 enc CCAO._kp{1}.`1 x.`1.`1 = CCAO._chal{1} /\ 
                 x.`1.`2 = CCAO._chal{1} /\ 
                 x.`2 = (CCAO._chal{1},CCAO._chal{1})) /\
    (forall c' x', c' <> CCAO._chal{1} =>  
           (G.g{1} (x',(c',c'))).`2 = RO_H1.hc{2} (c',c')) /\
           (forall x, RO_H.h{2} x = if G.inS{1} (x,(x.`2,x.`2)) 
                                    then (G.rep{1} (x,(x.`2,x.`2))).`1 
                                    else (G.g{1} (x,(x.`2,x.`2))).`1)).
 + by proc; inline *;auto => /> /#.
 + by proc; inline *;auto => /> /#.
 swap {1} 6 -4;rnd{1};wp;wp;rnd;wp;sp. 
 conseq (_:  (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 
                                      then kright{1} 
                                      else hc{1} cc) = RO_H1.hc{2}); 1: smt().
  transitivity {1} { Bridge.bL(enc pk m); } 
     (true ==> hc{1} = Bridge.hc0{2} /\ kright{1} = Bridge.kl{2} /\
       Bridge.hc{2} =  (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 then Bridge.kl{2} else Bridge.hc0{2} cc))
     ( ={pk,m} ==> ={pk,m} /\ RO_H1.hc{2} = Bridge.hc{1}); 1,2: smt(). 
  + by inline *; swap {1} 1 1;auto => />.
  transitivity {2} { Bridge.bR(); } 
     ( ={pk,m} ==> ={pk,m}  /\ ={Bridge.hc}) 
     (={pk,m} ==> ={pk,m}  /\ Bridge.hc{1} = RO_H1.hc{2} ) ; 1,2:  smt(). 
   conseq />; ecall (bridge (enc pk{2} m{2})); auto => />. 
  + by inline *; auto => />.
qed.


lemma red_works(B <: B_t {-OWReduction, -H}) &m:
   Pr [ B_O(H(I),B,Awrap(A)).main() @ &m : res] <=
   Pr [ OW(OWReduction(B,A)).main() @ &m : res].
proof.
byequiv => //.
proc; inline *;wp.
call(_: G.g{1} = OWReduction.g{2} /\
        G.rep{1} = OWReduction.rep{2} /\
        G.inS{1} = OWReduction.inS{2}).
+ by conseq />;sim.
by auto => />;smt(hasP nth_find).
qed.

lemma ow2h_hop  &m d :
    0 <= d =>
(forall (O <: CCAO_t) (H <: H_t), islossless H.o => islossless O.dec => islossless A(O,H).guess) =>
   (forall (O <: Gi_t), hoare[ A_O(Awrap(A), Count(O)).main : true ==> Count.ch <= d]) => 
    exists (B <: B_t {+Awrap(A)}),
   `| Pr[ RealIdeal1(RO_H1,RO_F,CCAO3,A).main(false) @ &m : res ] -
      Pr[ RealIdeal1(RO_H1,RO_F,CCAO3,A).main(true) @ &m : res ] | <=
         4%r * d%r * sqrt  Pr [ OW(OWReduction(B,A)).main() @ &m : res ].
proof. 
move => d_ge0 A_ll A_bnd (* FIXME: is this the way? *). 
have [B H] := ow2hsc1h I (Awrap(A) ) &m d _ _. 
+ by move => O O_ll;islossless;apply (A_ll (CCAO3(HWrap(O), (RO_F))) (HWrap(O)));islossless.
+ by apply A_bnd.
have <- := left_hop &m A_ll.
have <- := right_hop &m.
exists B.
have  := red_works B &m.
smt(ge0_sqrt rpow_hmono).
qed.

lemma main_theorem &m  d :
    0 <= d =>
(forall (O <: CCAO_t) (H <: H_t), islossless H.o => islossless O.dec => islossless A(O,H).guess) =>
   (forall (O <: Gi_t), hoare[ A_O(Awrap(A), Count(O)).main : true ==> Count.ch <= d]) => 
    exists (B <: B_t {+Awrap(A)}),
   `| Pr[ RealIdeal(RO_H,PRF,CCAO,A).main(false) @ &m : res ] -
      Pr[ RealIdeal(RO_H,PRF,CCAO,A).main(true) @ &m : res ] | <= 
       `|Pr[PRF_Security(PRF, D0(RO_H, A)).main()  @ &m : res ] -
           Pr[PRF_Security(RO_F, D0(RO_H, A)).main()  @ &m : res ] | +
       `|Pr[PRF_Security(PRF, D1(RO_H, A)).main()  @ &m : res ] -
           Pr[PRF_Security(RO_F, D1(RO_H, A)).main()  @ &m : res ] | +
       2%r * eps_injective + 
       Pr[FFC(B0(A)).main() @ &m : res] +
       Pr[FFC(B1(A)).main() @ &m : res] +
       4%r * d%r * sqrt Pr[OW(OWReduction(B,A)).main() @ &m : res ].
proof.
move => d_ge0 A_ll A_bnd.

have hop00_pr := (hop00_pr A &m).

have hop01_pr := (hop01_pr A &m).

have hop1_notbad_pr0 := (hop1_notbad_pr A &m false A_ll).
have hop1_notbad_pr1 := (hop1_notbad_pr A &m true A_ll).

have hop1_bad_pr1 := (hop1_bad_pr A  &m true A_ll).
have hop1_bad_pr0 := (hop1_bad_pr A  &m false A_ll).

have hop2_pr := (hop2_pr A &m).

move : (ow2h_hop &m d d_ge0 A_ll A_bnd).
move => [B HB].
exists B. 

have bad30_pr := (bad30_pr A &m).
have bad31_pr := (bad31_pr A &m).

have notbad3_pr1 := notbad3_pr A &m true A_ll.
have notbad3_pr0 := notbad3_pr A &m false A_ll.
smt().

qed.

end section.

end SemiClassicalBound.

theory TwoSidedBound.

clone import T_OW2H as TSOW2H with
  type X <- (msg * cph) * (cph * cph),
  type Y <- key * key,
  type Z <- pkey * key * cph,
  type W <- bool.  
import TwoSided.

module I : Init = {
  proc prm() : ((msg * cph) * (cph * cph) -> key * key) * 
               ((msg * cph) * (cph * cph) -> key * key) * 
               ((msg * cph) * (cph * cph) -> bool) * 
               (pkey * key * cph) * (bool -> bool) = {
     var pk, sk, m,c, h, hc,kleft, kright;
     (pk,sk) <$ kg;
     m <$ md;
     c <- enc pk m;
     hc <$ dhc;
     kleft <$ kd; 
     hc <- fun (cc : _*_) => if cc.`1 = c /\ cc.`1 = cc.`2
                            then kleft 
                            else hc cc;
     h <- fun (mc : (msg * cph)) => hc (enc pk mc.`1, mc.`2);
     kright <$ kd;     
     return (fun (x : (msg * cph) * (cph * cph)) => (h x.`1, hc x.`2), 
             fun (x : (msg * cph) * (cph * cph)) => (kright, kright), 
             fun (x : (msg * cph) * (cph * cph)) => enc pk x.`1.`1 = c /\ 
                                                    x.`1.`2 = c /\ 
                                                    x.`2 = (c,c), 
                          (pk, kleft, c), (fun b => b));
  }
}.

module HWrap(O : G_t) = {
     proc init(pk : pkey) = {}
     quantum proc o () {x : msg * cph}: key = {
         quantum var y;
         y <@ O.o{(x,(x.`2,x.`2))};
         return y.`1;
     }
     proc o2 (x : cph * cph): key = {
         var y;
         y <@ O.o{witness,x};
         return y.`2;
     }
}.

module (Awrap(A : CCAAdv_t) : A_t) (O : G_t)  = {
    
   proc run(z : pkey * key * cph) = {
      var pk, kleft,c, k1, b;
      b <- false;
      (pk, kleft, c) <- z;
      RO_F.init();
      CCAO._log <- [];
      CCAO._kp <- (pk,(pk,witness,witness));
      if (injective (enc CCAO._kp.`1)) {
         CCAO._chal <-  c;
         k1 <$ kd;
         b <@ A(CCAO3(HWrap(O),RO_F), HWrap(O)).guess(CCAO._kp.`1,kleft,c);
      }
      return b /\ injective (enc CCAO._kp.`1);
   }
}.

module OWReduction(B : B_t, A : CCAAdv_t) : OWAdv  = {
  (* This procedure is not efficient, but it is just
     preparing the random oracles, so they need to be
     replaced with efficient versions. This should  
     be OK. Apart from that, reduction just uses B. *)
  proc prm(pk : pkey, c : cph) : 
     ((msg * cph) * (cph * cph) -> key * key) * 
               ((msg * cph) * (cph * cph) -> key * key) * 
                ((msg * cph) * (cph * cph) -> bool) * 
               (pkey * key * cph) * unit = {
     var hc,h, kleft,kright;

     hc <$ dhc;
     kleft <$ kd; 
     hc <- fun (cc : _*_) => if cc.`1 = c /\ cc.`1 = cc.`2
                            then kleft 
                            else hc cc;
     h <- fun (mc : (msg * cph)) => hc (enc pk mc.`1, mc.`2);
     kright <$ kd;     
     return (fun (x : (msg * cph) * (cph * cph)) => (h x.`1, hc x.`2), 
             fun (x : (msg * cph) * (cph * cph)) => (kright, kright), 
             fun (x : (msg * cph) * (cph * cph)) => enc pk x.`1.`1 = c /\ 
                                                    x.`1.`2 = c /\ 
                                                    x.`2 = (c,c), 
                          (pk, kleft, c), ());
  }

  proc find(pk : pkey, c : cph) = {
      var z,ev, mc;
      (G.g,G.rep,G.inS,z,ev) <@ prm(pk,c);
      mc <@ B(GH(I),Awrap(A)).find(z);
      return mc.`1.`1;
  }
}.


section.

declare module A <: CCAAdv_t {-CCAO,  -G, -RO_F, -RO_H, -RO_H1, -H, -GH, -OWReduction, -PRF, -I}.



lemma left_hop &m :
  (forall (O <: CCAO_t) (H <: H_t), islossless H.o => islossless O.dec => islossless A(O,H).guess) =>
  Pr [ A_O(Awrap(A),G(I)).main() @ &m : res]  =
  Pr[RealIdeal1(RO_H1, RO_F, CCAO3, A).main(false) @ &m : res].
 proof. 
move => A_ll.
 byequiv => //.
 proc; inline*;wp.
 swap {2} 4 -3; seq 0 1 : #pre; 1: by auto.
 swap{1} [14..15] -13. 
 seq 3 3 : (#pre /\ ={CCAO._log,sk} /\ pk0{1} = pk{2}); 1: by auto.
 sp; if{2}; last first.
 + rcondf {1} 14; 1: by move => *; auto => />.
   by auto => />; smt(H1.dfun_ll kd_ll). 
 rcondt {1} 14; 1: by move => *; auto => />.
 swap {2} 5 -3; swap {2} 5 -3; sp; seq 1 1 : (#pre /\ ={m}); 1: by auto.
 call(_: ={CCAO._chal} /\ 
          CCAO._kp{1}.`1 = CCAO._kp{2}.`1 /\ 
          G.g{1} = fun (x : (msg * cph) * (cph * cph)) => (RO_H.h{2} x.`1, RO_H1.hc{2} x.`2)).
 + by proc; inline *;auto => />.
 + by proc; inline *;auto => />.
 wp;rnd;wp;rnd{1}; wp;sp.
 conseq (_:  (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 
                                      then kleft0{1} 
                                      else hc{1} cc) = RO_H1.hc{2}); 1: smt().
  transitivity {1} { Bridge.bL(enc pk m); } 
     (true ==> hc{1} = Bridge.hc0{2} /\ kleft0{1} = Bridge.kl{2} )
     ( ={pk,m} ==> RO_H1.hc{2} = (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 then Bridge.kl{1} else Bridge.hc0{1} cc)); 1,2: smt().
  + by inline *; auto => />.
  transitivity {2} { Bridge.bR(); } 
     ( ={pk,m} ==> ={pk,m}  /\ Bridge.hc{2} = (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 then Bridge.kl{1} else Bridge.hc0{1} cc)) 
     (={pk,m} ==> ={pk,m}  /\ Bridge.hc{1} = RO_H1.hc{2} ) ; 1,2:  smt(). 
   conseq />; ecall (bridge (enc pk{2} m{2})); auto => />. 
  + by inline *; auto => />.
qed.

lemma right_hop  &m :
  (forall (O <: CCAO_t) (H <: H_t), islossless H.o => islossless O.dec => islossless A(O,H).guess) =>
  Pr [ A_O(Awrap(A),H(I)).main() @ &m : res]  =
  Pr [ RealIdeal1(RO_H1,RO_F,CCAO3,A).main(true) @ &m : res].
 proof. 
move => A_ll.
 byequiv => //.
 proc; inline*;wp.
 swap {2} 4 -3; seq 0 1 : #pre; 1: by auto.
 swap{1} [14..15] -13. 
 seq 3 3 : (#pre /\ ={CCAO._log,sk} /\ pk0{1} = pk{2}); 1: by auto.
 sp; if{2}; last first.
 + rcondf {1} 14; 1: by move => *; auto => />.
   by auto => />; smt(H1.dfun_ll kd_ll). 
 rcondt {1} 14; 1: by move => *; auto => />.
 swap {2} 5 -3; swap {2} 5 -3; sp; seq 1 1 : (#pre /\ ={m}); 1: by auto.
 call(_: ={CCAO._chal} /\ CCAO._kp{1}.`1 = CCAO._kp{2}.`1 /\ 
     G.inS{1} = (fun (x : (msg * cph) * (cph * cph)) => 
                 enc CCAO._kp{1}.`1 x.`1.`1 = CCAO._chal{1} /\ 
                 x.`1.`2 = CCAO._chal{1} /\ 
                 x.`2 = (CCAO._chal{1},CCAO._chal{1})) /\
    (forall c' x', c' <> CCAO._chal{1} =>  
           (G.g{1} (x',(c',c'))).`2 = RO_H1.hc{2} (c',c')) /\
           (forall x, RO_H.h{2} x = if G.inS{1} (x,(x.`2,x.`2)) 
                                    then (G.rep{1} (x,(x.`2,x.`2))).`1 
                                    else (G.g{1} (x,(x.`2,x.`2))).`1)).
 + by proc; inline *;auto => /> /#.
 + by proc; inline *;auto => /> /#.
 swap {1} 6 -4;rnd{1};wp;wp;rnd;wp;sp. 
 conseq (_:  (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 
                                      then kright{1} 
                                      else hc{1} cc) = RO_H1.hc{2}); 1: smt().
  transitivity {1} { Bridge.bL(enc pk m); } 
     (true ==> hc{1} = Bridge.hc0{2} /\ kright{1} = Bridge.kl{2} )
     ( ={pk,m} ==> RO_H1.hc{2} = (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 then Bridge.kl{1} else Bridge.hc0{1} cc)); 1,2: smt().
  + by inline *; swap {1} 1 1 ;auto => />.
  transitivity {2} { Bridge.bR(); } 
     ( ={pk,m} ==> ={pk,m}  /\ Bridge.hc{2} = (fun (cc : cph * cph) => if cc.`1 = enc pk{2} m{2} /\ cc.`1 = cc.`2 then Bridge.kl{1} else Bridge.hc0{1} cc)) 
     (={pk,m} ==> ={pk,m}  /\ Bridge.hc{1} = RO_H1.hc{2} ) ; 1,2:  smt(). 
   conseq />; ecall (bridge (enc pk{2} m{2})); auto => />. 
  + by inline *; auto => />.
qed.


lemma red_works (B <: B_t {-OWReduction, -GH, -OW}) &m:
   Pr [ B_O(GH(I),B,Awrap(A)).main() @ &m : res] <=
   Pr [ OW(OWReduction(B,A)).main() @ &m : res ].
proof.
byequiv => //.
proc; inline *;wp.
call(_: ={G.g,G.rep,G.inS}).
+ by sim.
+ by sim.
by auto => />;smt().
qed.

lemma ow2h_hop  &m :
  (forall (O <: CCAO_t) (H <: H_t), islossless H.o => islossless O.dec => islossless A(O,H).guess) =>
    exists (B <: B_t {+Awrap(A)}),
   `| Pr[ RealIdeal1(RO_H1,RO_F,CCAO3,A).main(false) @ &m : res ] -
      Pr[ RealIdeal1(RO_H1,RO_F,CCAO3,A).main(true) @ &m : res ] | <=
         2%r * sqrt  (Pr [ OW(OWReduction(B,A)).main() @ &m : res ] + eps_injective).
proof. 
move => A_ll.
have [B H] := ow2h_2sided I (Awrap(A)) &m eps_injective _ _.
(* The current TwoSided lemma has been strengthened to allow an I
   with epsilon probability of providing a non singleton S.
   That bound must be checked or we should change this proof so
   that our init samples from a restricted distribution, but this
   can then create problems on how to have our reduction simulate
   the oracles. Room for thought here. *)
+ proc; wp; swap -7; wp; swap -5; swap -4; wp; swap -4;
    rnd (fun (kp : _*_) => injective (enc kp.`1));auto => />. 
  split; 1: smt(md_ll kd_ll H1.dfun_ll).
  move => ? v ??;split; 1: smt(md_ll kd_ll H1.dfun_ll).
  move => ? v0 ??;split; 1: smt(md_ll kd_ll H1.dfun_ll).
  move => ? v1 ?? v2 ??; split; rewrite /eps_injective /injective; 1: by  smt(kg_ll mu_not). 
  by move => ? v3 ? ?; exists((v,enc v3.`1 v),(enc v3.`1 v, enc v3.`1 v)); smt().
+ by move => O O_ll;islossless; apply (A_ll (CCAO3(HWrap(O), (RO_F))) (HWrap(O)));islossless.
exists B.
have <- := left_hop &m A_ll.
have <- := right_hop &m A_ll.
have  := red_works B &m.
smt(ge0_sqrt rpow_hmono).
qed.

lemma main_theorem &m :
  (forall (O <: CCAO_t) (H <: H_t), islossless H.o => islossless O.dec => islossless A(O,H).guess) =>
    exists (B <: B_t {+Awrap(A)}),
   `| Pr[ RealIdeal(RO_H,PRF,CCAO,A).main(false) @ &m : res ] -
      Pr[ RealIdeal(RO_H,PRF,CCAO,A).main(true) @ &m : res ] | <= 
       `|Pr[PRF_Security(PRF, D0(RO_H, A)).main()  @ &m : res ] -
           Pr[PRF_Security(RO_F, D0(RO_H, A)).main()  @ &m : res ] | +
       `|Pr[PRF_Security(PRF, D1(RO_H, A)).main()  @ &m : res ] -
           Pr[PRF_Security(RO_F, D1(RO_H, A)).main()  @ &m : res ] | +
       2%r * eps_injective +
       Pr[FFC(B0(A)).main() @ &m : res] +
       Pr[FFC(B1(A)).main() @ &m : res] +
       2%r * sqrt (Pr[OW(OWReduction(B,A)).main() @ &m : res ] + eps_injective).
proof.
move => A_ll.
have hop00_pr := (hop00_pr A &m).

have hop01_pr := (hop01_pr A &m).

have hop1_notbad_pr1 := (hop1_notbad_pr A &m true A_ll).
have hop1_notbad_pr0 := (hop1_notbad_pr A &m false A_ll).

have hop1_bad_pr1 := (hop1_bad_pr A &m true A_ll).
have hop1_bad_pr0 := (hop1_bad_pr A &m false A_ll).

have hop2_pr := (hop2_pr A &m).

move : (ow2h_hop &m A_ll).
move => [B HB].
exists B. 

have bad30_pr := (bad30_pr A &m).
have bad31_pr := (bad31_pr A &m).

have notbad3_pr0 := notbad3_pr A &m false A_ll.
have notbad3_pr1 := notbad3_pr A &m true A_ll.

smt().

qed.


end section.

end TwoSidedBound.

end U_Implicit.
