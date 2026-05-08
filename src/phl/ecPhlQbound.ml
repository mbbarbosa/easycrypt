open EcPath
open EcAst
open EcFol
open EcCoreGoal
open EcEnv
open EcCoreModules
open EcUtils
open EcDecl

(*let modtype_of_param_proc (params : (EcIdent.t * module_type) list) (xp : xpath) :  module_type option =
  let top = EcPath.m_functor xp.EcPath.x_top in
  match EcPath.mget_ident_opt top with
  | None -> None
  | Some pid ->
      Some (List.find_map (fun (id, mty) -> if EcIdent.id_equal id pid then Some mty else None) params)
*)
let check (a : EcDecl.axiom) (f : xpath) (o : xpath) (env : env) : bool =
  let form = a.ax_spec in
  match form.f_node with 
  | Fqbound qb -> 
    Format.eprintf "f' = %s\n%!" (EcFol.dump_f form);
    let s = f_bind_mod (f_subst_init ()) (mget_ident qb.qb_orcl.x_top) f.x_top env in
    let f' = EcCoreSubst.Fsubst.f_subst s form in
    Format.eprintf "f' = %s\n%!" (EcFol.dump_f f');
    begin
    match f'.f_node with     
      |Fqbound qb -> (*qmod_or_proc_equal qb.qb_proc (Qproc f) &&*) x_equal qb.qb_orcl o
      | _ -> assert false
    end
  | _ -> false

let sum_int_forms (fs : form list) : form =
  List.fold_left f_int_add_simpl f_i0 fs

let rec qbound (fb : stmt) (o : xpath) (env : env) =
  let is = fb.s_node in 
  let doit i =
    match i.i_node with
    | Scall (_, x, _) -> 
       let f' = Fun.by_xpath x env in
       begin
       if x_equal o x then f_i1
       else 
        match f'.f_def with
        | FBdef fdef -> qbound fdef.f_body o env 
        | FBabs oi -> 
          let oi = List.map (NormMp.norm_xfun env) oi.oi_calls in
          Format.eprintf "length : %s\n%!" (string_of_int (List.length oi));
          List.iter (fun (_,a) -> Format.eprintf "axioms: %s@." (EcFol.dump_f a.ax_spec)) (Ax.all ~check:(fun _ ax -> match ax.ax_loca with `Local | `Declare -> true | _ -> false) env);
          let l = List.snd (Ax.all ~check:(fun _ a -> List.exists (fun o' -> check a o o' env) oi) env) in
          let qbl = List.map (fun a -> match a.ax_spec.f_node with Fqbound qb -> qb.qb_bound | _ -> assert false) l in
          sum_int_forms qbl
        | _ -> assert false
        end 
    | _ -> f_i0
  in
  sum_int_forms (List.map doit is)

let process_qbound (tc : tcenv1) =
  let q = FApi.tc1_goal tc in
  let qb = match q.f_node with Fqbound qb -> qb.qb_bound | _ -> assert false in
  let env = FApi.tc1_env tc in
  let x = proc_of_qbound q in
  let o = orcl_of_qbound q in
  let x = match x with 
    | Qproc p -> p
    | Qmod _ -> assert false in
  let f = Fun.by_xpath x env in
  let sum = match f.f_def with | FBdef fb -> qbound fb.f_body o env | _ -> assert false in
  FApi.xmutate1 tc `Qbound [f_int_le qb sum]