(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr DBool  FunSamplingLib.
require (*--*) Matrix.

(* --- Local --- *)
require import SaberPKEPreliminaries.
(*---*) import Mat_Rq Mat_Rp. 
(*---*) import Rq Rp.
(*---*) import Rq.ComRing Rp.ComRing.

op [lossless full uniform] dseed : seed distr.

(* ----------------------------------- *)
(*  QROM                                *)
(* ----------------------------------- *)
require T_QROM.
clone import T_QROM as PR with
  type from <- seed,
  type hash <- Rq_mat,
  op dhash <- dRq_mat
  proof dhash_ll by exact: dRq_mat_ll
  proof dhash_uni by exact: dRq_mat_uni
  proof dhash_fu by exact: dRq_mat_fu.

(* Additional QROM variant to support history free proofs, 
   takes h as input to init *)
module QRO_hf : QRO  = {
   var h : seed -> Rq_mat
   proc init(h_in: seed -> Rq_mat) = { h <- h_in; }
   quantum proc h{ x : seed } : Rq_mat = { return h x; }
}.



(* ----------------------------------- *)
(*  Adversary Classes                  *)
(* ----------------------------------- *)
quantum module type Adv_MLWR = {
  proc guess(_A : Rq_mat, b : Rp_vec) : bool
}.

quantum module type Adv_MLWR1 = {
  proc guess(_A : Rq_mat, a : Rq_vec, b : Rp_vec, d : Rp) : bool
}.

quantum module type Adv_GMLWR_QRO(Gen : QRO) = {
   proc guess(sd : seed, b : Rp_vec) : bool { Gen.h }
}.

quantum module type Adv_XMLWR_QRO(Gen : QRO) = {
   proc guess(sd : seed, b : Rp_vec, a : Rq_vec, d : Rp) : bool { Gen.h }
}.

(* ----------------------------------- *)
(*  Games                              *)
(* ----------------------------------- *)

(* Original MLWR Game (l samples) *)
module MLWR(A : Adv_MLWR) = {
    proc main(u : bool) : bool = {
       var u' : bool;
       var _A : Rq_mat;
       var s : Rq_vec;
       var b : Rp_vec;

       _A <$ dRq_mat;
       s <$ dsmallRq_vec;
       
       if (u) {
          b <$ dRp_vec; 
       } else {
          b <- scaleroundRqv2Rpv (_A *^ s);
       }
       
       u' <@ A.guess(_A, b);

       return u';
    }
}.

(* Original MLWR Game (l + 1 samples) *)
module MLWR1(A : Adv_MLWR1) = {
    proc main(u : bool) : bool = {
       var u' : bool;
       var _A : Rq_mat;
       var a : Rq_vec;
       var s : Rq_vec;
       var b : Rp_vec;
       var d : Rp;

       _A <$ dRq_mat; (* l samples *)
       a <$ dRq_vec; (* single sample *)
      
       s <$ dsmallRq_vec;
       
       if (u) {
          b <$ dRp_vec;
          d <$ dRp;
       } else {
          b <- scaleroundRqv2Rpv (_A *^ s);
          d <- scaleroundRq2Rp (dotp a s);
       }
       
       u' <@ A.guess(_A, a, b, d);

       return u';
    }
}.

(* GMLWR in ROM *)
module GMLWR_QRO(A : Adv_GMLWR_QRO) = {
   module A = A(QRO)

   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;

      QRO.init();

      sd <$ dseed;
      _A <@ QRO.h{ sd };
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleroundRqv2Rpv (_A *^ s);
      }
      
      u' <@ A.guess(sd, b);
      
      return u';
   }
}.


(* XMLWR in QROM *)
module XMLWR_QRO(A : Adv_XMLWR_QRO) = {
   module A = A(QRO)

   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      var a : Rq_vec;
      var d : Rp;

      QRO.init();

      sd <$ dseed;
      _A <@ QRO.h { sd };
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleroundRqv2Rpv ((trmx _A) *^ s);
      }
      
      a <$ dRq_vec;

      if (u) {
         d <$ dRp;
      } else {
         d <- scaleroundRq2Rp (dotp a s);
      }
    
      u' <@ A.guess(sd, b, a, d);
      
      return u';
   }
}.

(* --------------------------------------- *)
(*  Intermediate games to match sampling   *)
(* --------------------------------------- *)

clone import PointResampling with
  type X <- seed,
  type Y <- Rq_mat,
  op dy <- dRq_mat,
  theory MUFF <- MUFF
  proof dy_ll by exact: dRq_mat_ll.

module GMLWR_left(A : Adv_GMLWR_QRO) = {
   module A = A(QRO_hf)

   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      var h : seed -> Rq_mat;

      PointRS.left();
      QRO_hf.init(PointRS.h);

      sd <$ dseed;
      _A <@ QRO_hf.h{ sd };
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleroundRqv2Rpv (_A *^ s);
      }
      
      u' <@ A.guess(sd, b);
      
      return u';
   }
}.

module GMLWR_right(A : Adv_GMLWR_QRO) = {
   module A = A(QRO_hf)

   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      var h : seed -> Rq_mat;

      sd <$ dseed;
      PointRS.right(sd);
      QRO_hf.init(PointRS.h);

      _A <@ QRO_hf.h{ sd };
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleroundRqv2Rpv (_A *^ s);
      }
      
      u' <@ A.guess(sd, b);
      
      return u';
   }
}.

module XMLWR_left(A : Adv_XMLWR_QRO) = {
   module A = A(QRO_hf)

   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      var a : Rq_vec;
      var d : Rp;

      
      PointRS.left();
      QRO_hf.init(PointRS.h);
      
      sd <$ dseed;
      _A <@ QRO_hf.h { sd };
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleroundRqv2Rpv ((trmx _A) *^ s);
      }
      
      a <$ dRq_vec;

      if (u) {
         d <$ dRp;
      } else {
         d <- scaleroundRq2Rp (dotp a s);
      }
    
      u' <@ A.guess(sd, b, a, d);
      
      return u';
   }
}.

module XMLWR_right(A : Adv_XMLWR_QRO) = {
   module A = A(QRO_hf)

   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      var a : Rq_vec;
      var d : Rp;

      
      sd <$ dseed;
      PointRS.right(sd);
      QRO_hf.init(PointRS.h);
      
      _A <@ QRO_hf.h { sd };
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleroundRqv2Rpv ((trmx _A) *^ s);
      }
      
      a <$ dRq_vec;

      if (u) {
         d <$ dRp;
      } else {
         d <- scaleroundRq2Rp (dotp a s);
      }
    
      u' <@ A.guess(sd, b, a, d);
      
      return u';
   }
}.


(* ----------------------------------- *)
(*  Reduction Adversaries              *)
(* ----------------------------------- *)

(* Adversary Against MLWR (l samples) Game, Constructed From Adversary Against GMLWR_RO Game *)
module AGM(AG : Adv_GMLWR_QRO) : Adv_MLWR = {
   module AG = AG(QRO_hf)

   proc guess(_A : Rq_mat, b : Rp_vec) : bool = {
      var u' : bool;
      var sd : seed;
      var f,h: seed -> Rq_mat;
      
      sd <$ dseed;
      f <$ dh;
      h  <-  fun x => if x = sd then _A else f x;

      QRO_hf.init(h);
      
      u' <@ AG.guess(sd, b);

      return u';
   } 
}.

(* Adversary Against MLWR1 (l + 1 samples) Game, Constructed From Adversary Against XMLWR_RO Game *)
module AXM(AX : Adv_XMLWR_QRO) : Adv_MLWR1 = {
   module AX = AX(QRO_hf)

   proc guess(_A : Rq_mat, a : Rq_vec, b : Rp_vec, d : Rp) : bool = {
      var u' : bool;
      var sd : seed;

      var f,h: seed -> Rq_mat;
      
      sd <$ dseed;
      f <$ dh;
      h  <-  fun x => if x = sd then trmx _A else f x;

      QRO_hf.init(h);

      u' <@ AX.guess(sd, b, a, d);

      return u';
   } 
}.

(* ----------------------------------- *)
(*  Reductions                         *)
(* ----------------------------------- *)

(* First trivial game hop *)
lemma Equivalent_GMLWR_QRO_GMLWR_left (A <: Adv_GMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  equiv[GMLWR_QRO(A).main ~ GMLWR_left(A).main : ={glob A, u} ==> ={res}].
proof.
proc. inline*. sim. auto.  
qed.

(* Second game hop (using point resampling).*)
lemma Equivalent_GMLWR_left_GMLWR_right (A <: Adv_GMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  equiv[GMLWR_left(A).main ~ GMLWR_right(A).main : ={glob A, u} ==> ={res}].
proof.
proc. 
swap {1} 3 -2.
seq 1 1 : (#pre /\ ={sd}). by rnd. 
seq 1 1 : (#pre /\ ={PointRS.h}). 
+ call main_theorem. by skip.
call ( : ={QRO_hf.h}). by sim.
seq 3 3 : (#pre /\ ={ QRO_hf.h, _A, s}).
+ by inline*; auto.
by if; auto. 
qed.

(* Reduction From GMLWR_QRO to MLWR *)
lemma Equivalent_GMLWR_right_MLWR (A <: Adv_GMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  equiv[GMLWR_right(A).main ~ MLWR( AGM(A) ).main : ={glob A, u} ==> ={res}].
proof.
proc; inline *.
case (u{1}).
+ conseq (_ : ={glob A} /\ u{1} /\ u{2} ==> _) => //.
  rcondt {1} 11; 2: rcondt {2} 3; first 2 by auto.
  wp. call ( : ={QRO_hf.h}) => /=.
  + proc. by skip. 
  + wp. swap{1} [10..11] -8. swap {2} 6 -5. swap{2} 2 2. wp. rnd. wp.
rnd. wp. by auto => />. 

+ conseq (_ :  ={glob A} /\ !u{1} /\ !u{2} ==> _) => //. 
  rcondf {1} 11; 2: rcondf {2} 3; first 2 by auto.
  swap {1} 10 -8; swap {2} 6 -5; swap {2} 3 -1.
  wp; call (_ : ={QRO_hf.h}).
  by sim. 
by auto. 
qed.

(* Theorem: MLWR => GMLWR in QROM *)
lemma Equivalent_GMLWR_QRO_MLWR (A <: Adv_GMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  equiv[GMLWR_QRO(A).main ~  MLWR( AGM(A) ).main : ={glob A, u} ==> ={res}].
proof.
transitivity GMLWR_left(A).main (={glob A, u} ==> ={res}) ( ={glob A, u} ==> ={res}) => //.
by smt().
by apply (Equivalent_GMLWR_QRO_GMLWR_left A).
transitivity GMLWR_right(A).main (={glob A, u} ==> ={res}) ( ={glob A, u} ==> ={res}) => //.
by smt().
by apply (Equivalent_GMLWR_left_GMLWR_right A).
by apply (Equivalent_GMLWR_right_MLWR A).
qed.                    
          
lemma Equal_Advantage_GMLWR_QRO_MLWR &m (A <: Adv_GMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  `| Pr[GMLWR_QRO(A).main(true) @ &m : res] - Pr[GMLWR_QRO(A).main(false) @ &m : res] |
   =
  `| Pr[MLWR( AGM(A) ).main(true) @ &m : res] - Pr[MLWR( AGM(A) ).main(false) @ &m : res] |.
proof.
have ->: Pr[GMLWR_QRO(A).main(true) @ &m : res] = Pr[MLWR( AGM(A) ).main(true) @ &m : res].
+ by byequiv (Equivalent_GMLWR_QRO_MLWR A).
have -> //: Pr[GMLWR_QRO(A).main(false) @ &m : res] = Pr[MLWR( AGM(A) ).main(false) @ &m : res].
+ by byequiv (Equivalent_GMLWR_QRO_MLWR A).
qed.

(******************* GMLWR  Reduction done ********************)

(*********************** XMLWR reduction **********************)
(* First trivial game hop *)
lemma Equivalent_XMLWR_QRO_XMLWR_left (A <: Adv_XMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  equiv[XMLWR_QRO(A).main ~ XMLWR_left(A).main : ={glob A, u} ==> ={res}].
proof.
by proc; inline*; sim; auto. 
qed.

(* Second game hop (using point resampling).*)
lemma Equivalent_XMLWR_left_XMLWR_right (A <: Adv_XMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  equiv[XMLWR_left(A).main ~ XMLWR_right(A).main : ={glob A, u} ==> ={res}].
proof.
proc. 
swap {1} 3 -2.
seq 1 1 : (#pre /\ ={sd}). by rnd. 
seq 1 1 : (#pre /\ ={PointRS.h}). 
+ call main_theorem. by skip.
call ( : ={QRO_hf.h}). by sim.
seq 3 3 : (#pre /\ ={ QRO_hf.h, _A, s}).
+ by inline*; auto.
if; first by auto. 
seq 2 2 : (#pre /\ ={a,b}); first by auto. 
by if; auto. 
seq 2 2 : (#pre /\ ={a,b}); first by auto. 
by if; auto.
qed.

(* Reduction From XMLWR_QRO to MLWR with l+1 samples *)
lemma Equivalent_XMLWR_right_MLWR1 (A <: Adv_XMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  equiv[XMLWR_right(A).main ~ MLWR1( AXM(A) ).main : ={glob A, u} ==> ={res}].
proof.
proc; inline *.
case (u{1}).
+ conseq (_ : ={glob A} /\ u{1} /\ u{2} ==> _) => //.
  rcondt {1} 11; 2: rcondt {2} 4; first 2 by auto.
  rcondt {1} 13; first by auto.
  wp; call ( : ={QRO_hf.h}) => /=.
  + proc. by skip. 
  + wp; swap{1} [10..13] -9; swap {2} 1 4; swap{2} 2-1; swap {1} 2 1; swap{2} 10 -5; wp; rnd. 
  wp; rnd (fun (m : Rq_mat) => trmx m); wp; auto => />. 
 move => * />.  (*&1 &2 pre aL bL aR bR dL dR dR_H1 dleft dleft_H1 sdl sdl_H.*) 
 progress => />; by rewrite trmxK.
  
conseq (_ :  ={glob A} /\ !u{1} /\ !u{2} ==> _) => //. 
rcondf {1} 11; 2: rcondf {2} 4; 3: rcondf {1} 13; first 3 by auto.
wp; call (_ : ={QRO_hf.h}); first by sim.
wp; swap{2} 10 -9; swap {1} 12 -10; swap {1} 11 -9; swap {2} 4 -2; swap {2} 4 -1.
wp; rnd; wp; rnd (fun (m : Rq_mat) => trmx m).
wp; auto => />. 
move => * />; progress; by rewrite trmxK. 
qed.

(* Theorem: MLWR1 => XMLWR in QROM *)
lemma Equivalent_XMLWR_QRO_MLWR1 (A <: Adv_XMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  equiv[XMLWR_QRO(A).main ~  MLWR1( AXM(A) ).main : ={glob A, u} ==> ={res}].
proof.
transitivity XMLWR_left(A).main (={glob A, u} ==> ={res}) ( ={glob A, u} ==> ={res}) => //.
by smt().
by apply (Equivalent_XMLWR_QRO_XMLWR_left A).
transitivity XMLWR_right(A).main (={glob A, u} ==> ={res}) ( ={glob A, u} ==> ={res}) => //.
by smt().
by apply (Equivalent_XMLWR_left_XMLWR_right A).
by apply (Equivalent_XMLWR_right_MLWR1 A).
qed.                    
          
lemma Equal_Advantage_XMLWR_QRO_MLWR1 &m (A <: Adv_XMLWR_QRO{-QRO_hf, -QRO, -PointRS}) :
  `| Pr[XMLWR_QRO(A).main(true) @ &m : res] - Pr[XMLWR_QRO(A).main(false) @ &m : res] |
   =
  `| Pr[MLWR1( AXM(A) ).main(true) @ &m : res] - Pr[MLWR1( AXM(A) ).main(false) @ &m : res] |.
proof.
have ->: Pr[XMLWR_QRO(A).main(true) @ &m : res] = Pr[MLWR1( AXM(A) ).main(true) @ &m : res].
+ by byequiv (Equivalent_XMLWR_QRO_MLWR1 A).
have -> //: Pr[XMLWR_QRO(A).main(false) @ &m : res] = Pr[MLWR1( AXM(A) ).main(false) @ &m : res].
+ by byequiv (Equivalent_XMLWR_QRO_MLWR1 A).
qed.
