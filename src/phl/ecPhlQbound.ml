open EcPath
open EcAst
open EcFol
open EcCoreGoal
open EcEnv
open EcCoreModules
open EcUtils
open EcDecl

(*

QUANTUM COST LOGIC

def workerProcConcrete:
-> fold over all instructions:
        - no call => accumulate 0
        - concrete call => recursively compute with result eC
                           if callee is classical, accumulate eC
                           if callee is quantum, accumulate Cmag eC
        - abstract call => call workerProcAbstract with result eC
                           if caller is classical, accumulate eC
                           if caller is quantum, accumulate Cmag eC

def workerProcAbstract:
       fold over all oracles Oi
       - Oi concrete: call workerProcConcrete with result eC
         if eC <> 0, check whether qOi is defined, and abort if not
         if callee is classical, accumulate qOi * eC
         if callee is quantum, accumulate qOi Cmag eC
       - Oi abstract: call workerProcAbstract with result eC
         if eC <> 0, check whether qOi is defined, and abort if not
         if callee is classical, accumulate qOi * eC
         if callee is quantum, accumulate qOi Cmag eC
*)
let two = f_int(EcBigInt.of_int 2)

let rec strip_forall (f : form) : form =
  match f.f_node with
  | Fquant (Lforall, _, f') -> strip_forall f'
  | _ -> f

let check (a : EcDecl.axiom) (callee : xpath) (f : xpath) (o : xpath) (env : env) : bool =
  let form = strip_forall a.ax_spec in
  match form.f_node with
  | Fqbound qb ->(*
    begin 
      Format.eprintf "[qbound-check] qb.proc=%s qb.orcl=%s qb.bound=%s@."
        (EcPath.x_tostring qb.qb_proc)
        (EcPath.x_tostring qb.qb_orcl)
        (EcFol.dump_f qb.qb_bound);
      Format.eprintf "[qbound-check] callee=%s@." (EcPath.x_tostring callee);
      Format.eprintf "[qbound-check] f=%s@." (EcPath.x_tostring f);

      let sin1 = NormMp.sig_of_mp env callee.x_top in
      let sin2 = NormMp.sig_of_mp env f.x_top in
      let me1, _ = Mod.by_mpath qb.qb_proc.x_top env in
      let me2, _ = Mod.by_mpath qb.qb_orcl.x_top env in
      let mt1, mt2 =
        match me1.me_body, me2.me_body with
        | ME_Decl mty1, ME_Decl mty2 -> mty1, mty2
        | _ -> assert false
      in

      (* Match both module type and called procedure/oracle symbols. *)
      try
        EcTyping.check_modtype env callee.x_top sin1 mt1;
        EcTyping.check_modtype env f.x_top sin2 mt2;
        EcSymbols.sym_equal callee.x_sub qb.qb_proc.x_sub
        && EcSymbols.sym_equal f.x_sub qb.qb_orcl.x_sub
      with
      | _ -> false
    end *)
    let m = qb.qb_orcl.x_top in
    let f' =
    if is_abstract m then
    begin
    let s = f_bind_mod (f_subst_init ()) (mget_ident qb.qb_orcl.x_top) f.x_top env in
    EcCoreSubst.Fsubst.f_subst s form 
    end
    else form in
    Format.eprintf "f'2 = %s\n%!" (EcFol.dump_f f');
    begin
    match (strip_forall f').f_node with     
      |Fqbound qb -> (*qmod_or_proc_equal qb.qb_proc (Qproc callee) &&*) x_equal qb.qb_orcl o && EcSymbols.sym_equal callee.x_sub qb.qb_proc.x_sub
      | _ -> assert false
    end
  | _ -> false

let sum_int_forms (fs : form list) : form =
  List.fold_left f_int_add_simpl f_i0 fs

let rec qbound_concrete (fb : stmt) (o : xpath) (env : env) =
  let is = fb.s_node in 
  let doit i =
    match i.i_node with
    | Scall (_, x, _) -> 

       let x = NormMp.norm_xfun env x in
       Format.eprintf "[debug] xpath x: %s\n%!" (EcPath.x_tostring x);
       let f' = Fun.by_xpath x env in
       begin
       let cmag = if f'.f_quantum = `Quantum then two else f_i1 in
       if x_equal o x then f_i1
       else
        match f'.f_def with
        | FBdef fdef -> f_int_mul_simpl cmag (qbound_concrete fdef.f_body o env)
        | FBabs oi -> (*List.iter (fun x -> Format.eprintf "oracle : %s\n%!" (EcPath.x_tostring x)) oi.oi_calls;*)
                      f_int_mul_simpl cmag (qbound_abstract x oi o env)
        | _ -> assert false
        end 
    | _ -> f_i0
  in
  sum_int_forms (List.map doit is)

and qbound_abstract (callee : xpath) (ois : oracle_info) (o : xpath) (env : env) =
  let ois = List.map (NormMp.norm_xfun env) ois.oi_calls in
  List.iter (fun x -> Format.eprintf "oracle : %s\n%!" (EcPath.x_tostring x)) ois;
  let doit oi =
    
    let oi = NormMp.norm_xfun env oi in
    Format.eprintf "[debug] xpath oi: %s\n%!" (EcPath.x_tostring oi);
    let f = Fun.by_xpath oi env in
    (*Format.eprintf "quantum : %a\n%!" EcPrinting.pp_quantum f.f_quantum;*)
    let cmag = if f.f_quantum = `Quantum then two else f_i1 in
    (*Format.eprintf "cmag: %s\n%!" (EcFol.dump_f cmag);*)
    let qo =
    match f.f_def with
    | FBdef fdef -> f_int_mul_simpl cmag (qbound_concrete fdef.f_body o env)
    | FBabs ois -> f_int_mul_simpl cmag (qbound_abstract oi ois o env)
    | _ ->  assert false
    in
    let l = List.snd (Ax.all ~check:(fun _ a -> List.exists (fun o' -> check a callee o' oi env && not (x_equal o o')) ois) env) in
    if List.is_empty l then f_i0
    else
    match (strip_forall (List.hd l).ax_spec).f_node with Fqbound qb -> Format.eprintf "hit! \n%!"; f_int_mul qb.qb_bound qo | _ -> assert false
  in
  let l = List.snd (Ax.all ~check:(fun _ a -> List.exists (fun o' -> check a callee o' o env) ois) env) in
  let qb = if List.is_empty l then f_i0 else
    match (strip_forall (List.hd l).ax_spec).f_node with Fqbound qb -> qb .qb_bound| _ -> assert false in
  sum_int_forms (List.map doit ois) |> f_int_add_simpl qb


let process_qbound (tc : tcenv1) =
  let q = FApi.tc1_goal tc in
  let qb = match q.f_node with Fqbound qb -> qb.qb_bound | _ -> assert false in
  let env = FApi.tc1_env tc in
  let x = proc_of_qbound q in
  let o = orcl_of_qbound q in
  let f = Fun.by_xpath x env in
  let rec body f = match f.f_def with | FBdef fb -> fb.f_body | FBalias x -> body (Fun.by_xpath x env) | _ -> assert false in
  let sum = match f.f_def with | FBabs ois -> qbound_abstract x ois o env | _ -> qbound_concrete (body f) o env in
  FApi.xmutate1 tc `Qbound [(f_int_le sum qb)]