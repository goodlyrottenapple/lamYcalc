theory LamTest
imports "../Nominal2" 
begin

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  bind x in l


ML {*

val trace = Unsynchronized.ref false
fun trace_msg msg = if ! trace then tracing (msg ()) else ()

val boolT = HOLogic.boolT
val mk_eq = HOLogic.mk_eq

open Function_Lib
open Function_Common

datatype globals = Globals of
 {fvar: term,
  domT: typ,
  ranT: typ,
  h: term,
  y: term,
  x: term,
  z: term,
  a: term,
  P: term,
  D: term,
  Pbool:term}

datatype rec_call_info = RCInfo of
 {RIvs: (string * typ) list,  (* Call context: fixes and assumes *)
  CCas: thm list,
  rcarg: term,                 (* The recursive argument *)
  llRI: thm,
  h_assum: term}


datatype clause_context = ClauseContext of
 {ctxt : Proof.context,
  qs : term list,
  gs : term list,
  lhs: term,
  rhs: term,
  cqs: cterm list,
  ags: thm list,
  case_hyp : thm}


fun transfer_clause_ctx thy (ClauseContext { ctxt, qs, gs, lhs, rhs, cqs, ags, case_hyp }) =
  ClauseContext { ctxt = ProofContext.transfer thy ctxt,
    qs = qs, gs = gs, lhs = lhs, rhs = rhs, cqs = cqs, ags = ags, case_hyp = case_hyp }


datatype clause_info = ClauseInfo of
 {no: int,
  qglr : ((string * typ) list * term list * term * term),
  cdata : clause_context,
  tree: Function_Ctx_Tree.ctx_tree,
  lGI: thm,
  RCs: rec_call_info list}
*}

thm accp_induct_rule

ML {*
(* Theory dependencies. *)
val acc_induct_rule = @{thm accp_induct_rule}

val ex1_implies_ex = @{thm FunDef.fundef_ex1_existence}
val ex1_implies_un = @{thm FunDef.fundef_ex1_uniqueness}
val ex1_implies_iff = @{thm FunDef.fundef_ex1_iff}

val acc_downward = @{thm accp_downward}
val accI = @{thm accp.accI}
val case_split = @{thm HOL.case_split}
val fundef_default_value = @{thm FunDef.fundef_default_value}
val not_acc_down = @{thm not_accp_down}
*}


ML {*
fun find_calls tree =
  let
    fun add_Ri (fixes,assumes) (_ $ arg) _ (_, xs) =
      ([], (fixes, assumes, arg) :: xs)
      | add_Ri _ _ _ _ = raise Match
  in
    rev (Function_Ctx_Tree.traverse_tree add_Ri tree [])
  end
*}

ML {*
fun mk_eqvt_at (f_trm, arg_trm) =
  let
    val f_ty = fastype_of f_trm
    val arg_ty = domain_type f_ty
  in
    Const (@{const_name eqvt_at}, [f_ty, arg_ty] ---> @{typ bool}) $ f_trm $ arg_trm
    |> HOLogic.mk_Trueprop
  end
*}

ML {*
fun find_calls2 f t = 
  let
    fun aux (g $ arg) = aux g #> aux arg #> (if f = g then cons ((g, arg)) else I)
      | aux (Abs (_, _, t)) = aux t 
      | aux _ = I
  in
    aux t []
  end 
*}


ML {*
(** building proof obligations *)

fun mk_compat_proof_obligations domT ranT fvar f glrs =
  let
    fun mk_impl ((qs, gs, lhs, rhs), (qs', gs', lhs', rhs')) =
      let
        val shift = incr_boundvars (length qs')

        val RCs_rhs  = find_calls2 fvar rhs
        val RCs_rhs' = find_calls2 fvar rhs'
      in
        Logic.mk_implies
          (HOLogic.mk_Trueprop (HOLogic.eq_const domT $ shift lhs $ lhs'),
            HOLogic.mk_Trueprop (HOLogic.eq_const ranT $ shift rhs $ rhs'))
        |> fold_rev (curry Logic.mk_implies) (map shift gs @ gs')
        |> fold_rev (curry Logic.mk_implies) (map (shift o mk_eqvt_at) RCs_rhs) (* HERE *) 
        (*|> fold_rev (curry Logic.mk_implies) (map mk_eqvt_at RCs_rhs')*) (* HERE *) 
        |> fold_rev (fn (n,T) => fn b => Term.all T $ Abs(n,T,b)) (qs @ qs')
        |> curry abstract_over fvar
        |> curry subst_bound f
      end
  in
    map mk_impl (unordered_pairs glrs)
  end
*}

ML {*
fun mk_completeness (Globals {x, Pbool, ...}) clauses qglrs =
  let
    fun mk_case (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) =
      HOLogic.mk_Trueprop Pbool
      |> curry Logic.mk_implies (HOLogic.mk_Trueprop (mk_eq (x, lhs)))
      |> fold_rev (curry Logic.mk_implies) gs
      |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
  in
    HOLogic.mk_Trueprop Pbool
    |> fold_rev (curry Logic.mk_implies o mk_case) (clauses ~~ qglrs)
    |> mk_forall_rename ("x", x)
    |> mk_forall_rename ("P", Pbool)
  end
*}

(** making a context with it's own local bindings **)
ML {*

fun mk_clause_context x ctxt (pre_qs,pre_gs,pre_lhs,pre_rhs) =
  let
    val (qs, ctxt') = Variable.variant_fixes (map fst pre_qs) ctxt
      |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs

    val thy = ProofContext.theory_of ctxt'

    fun inst t = subst_bounds (rev qs, t)
    val gs = map inst pre_gs
    val lhs = inst pre_lhs
    val rhs = inst pre_rhs

    val cqs = map (cterm_of thy) qs
    val ags = map (Thm.assume o cterm_of thy) gs

    val case_hyp = Thm.assume (cterm_of thy (HOLogic.mk_Trueprop (mk_eq (x, lhs))))
  in
    ClauseContext { ctxt = ctxt', qs = qs, gs = gs, lhs = lhs, rhs = rhs,
      cqs = cqs, ags = ags, case_hyp = case_hyp }
  end
*}

ML {*
(* lowlevel term function. FIXME: remove *)
fun abstract_over_list vs body =
  let
    fun abs lev v tm =
      if v aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (lev + 1) v t)
        | t $ u => abs lev v t $ abs lev v u
        | t => t)
  in
    fold_index (fn (i, v) => fn t => abs i v t) vs body
  end



fun mk_clause_info globals G f no cdata qglr tree RCs GIntro_thm RIntro_thms =
  let
    val Globals {h, ...} = globals

    val ClauseContext { ctxt, qs, cqs, ags, ... } = cdata
    val cert = Thm.cterm_of (ProofContext.theory_of ctxt)

    (* Instantiate the GIntro thm with "f" and import into the clause context. *)
    val lGI = GIntro_thm
      |> Thm.forall_elim (cert f)
      |> fold Thm.forall_elim cqs
      |> fold Thm.elim_implies ags

    fun mk_call_info (rcfix, rcassm, rcarg) RI =
      let
        val llRI = RI
          |> fold Thm.forall_elim cqs
          |> fold (Thm.forall_elim o cert o Free) rcfix
          |> fold Thm.elim_implies ags
          |> fold Thm.elim_implies rcassm

        val h_assum =
          HOLogic.mk_Trueprop (G $ rcarg $ (h $ rcarg))
          |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
          |> fold_rev (Logic.all o Free) rcfix
          |> Pattern.rewrite_term (ProofContext.theory_of ctxt) [(f, h)] []
          |> abstract_over_list (rev qs)
      in
        RCInfo {RIvs=rcfix, rcarg=rcarg, CCas=rcassm, llRI=llRI, h_assum=h_assum}
      end

    val RC_infos = map2 mk_call_info RCs RIntro_thms
  in
    ClauseInfo {no=no, cdata=cdata, qglr=qglr, lGI=lGI, RCs=RC_infos,
      tree=tree}
  end
*}

ML {*
fun store_compat_thms 0 thms = []
  | store_compat_thms n thms =
  let
    val (thms1, thms2) = chop n thms
  in
    (thms1 :: store_compat_thms (n - 1) thms2)
  end
*}

ML {*
(* expects i <= j *)
fun lookup_compat_thm i j cts =
  nth (nth cts (i - 1)) (j - i)

(* Returns "Gsi, Gsj, lhs_i = lhs_j |-- rhs_j_f = rhs_i_f" *)
(* if j < i, then turn around *)
fun get_compat_thm thy cts eqvtsi eqvtsj i j ctxi ctxj =
  let
    val ClauseContext {cqs=cqsi,ags=agsi,lhs=lhsi,...} = ctxi
    val ClauseContext {cqs=cqsj,ags=agsj,lhs=lhsj,...} = ctxj

    val lhsi_eq_lhsj = cterm_of thy (HOLogic.mk_Trueprop (mk_eq (lhsi, lhsj)))
  in if j < i then
    let
      val compat = lookup_compat_thm j i cts
    in
      compat         (* "!!qj qi. Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
      |> fold Thm.forall_elim (cqsj @ cqsi) (* "Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
      |> fold Thm.elim_implies (rev eqvtsj) (* HERE *)
      |> fold Thm.elim_implies agsj
      |> fold Thm.elim_implies agsi
      |> Thm.elim_implies ((Thm.assume lhsi_eq_lhsj) RS sym) (* "Gsj, Gsi, lhsi = lhsj |-- rhsj = rhsi" *)
    end
    else
    let
      val compat = lookup_compat_thm i j cts
    in
      compat        (* "!!qi qj. Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
      |> fold Thm.forall_elim (cqsi @ cqsj) (* "Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
      |> fold Thm.elim_implies (rev eqvtsi)  (* HERE *)
      |> fold Thm.elim_implies agsi
      |> fold Thm.elim_implies agsj
      |> Thm.elim_implies (Thm.assume lhsi_eq_lhsj)
      |> (fn thm => thm RS sym) (* "Gsi, Gsj, lhsi = lhsj |-- rhsj = rhsi" *)
    end
  end
*}


ML {*
(* Generates the replacement lemma in fully quantified form. *)
fun mk_replacement_lemma thy h ih_elim clause =
  let
    val ClauseInfo {cdata=ClauseContext {qs, cqs, ags, case_hyp, ...},
      RCs, tree, ...} = clause
    local open Conv in
      val ih_conv = arg1_conv o arg_conv o arg_conv
    end

    val ih_elim_case =
      Conv.fconv_rule (ih_conv (K (case_hyp RS eq_reflection))) ih_elim

    val Ris = map (fn RCInfo {llRI, ...} => llRI) RCs
    val h_assums = map (fn RCInfo {h_assum, ...} =>
      Thm.assume (cterm_of thy (subst_bounds (rev qs, h_assum)))) RCs

    val (eql, _) =
      Function_Ctx_Tree.rewrite_by_tree thy h ih_elim_case (Ris ~~ h_assums) tree

    val replace_lemma = (eql RS meta_eq_to_obj_eq)
      |> Thm.implies_intr (cprop_of case_hyp)
      |> fold_rev (Thm.implies_intr o cprop_of) h_assums
      |> fold_rev (Thm.implies_intr o cprop_of) ags
      |> fold_rev Thm.forall_intr cqs
      |> Thm.close_derivation
  in
    replace_lemma
  end
*}

ML {*
fun mk_eqvt_lemma thy ih_eqvt clause =
  let
    val ClauseInfo {cdata=ClauseContext {cqs, ags, case_hyp, ...}, RCs, ...} = clause

    local open Conv in
      val ih_conv = arg1_conv o arg_conv o arg_conv
    end

    val ih_eqvt_case =
      Conv.fconv_rule (ih_conv (K (case_hyp RS eq_reflection))) ih_eqvt

    fun prep_eqvt (RCInfo {llRI, RIvs, CCas, ...}) = 
        (llRI RS ih_eqvt_case)
        |> fold_rev (Thm.implies_intr o cprop_of) CCas
        |> fold_rev (Thm.forall_intr o cterm_of thy o Free) RIvs
  in
    map prep_eqvt RCs
    |> map (fold_rev (Thm.implies_intr o cprop_of) ags)
    |> map (Thm.implies_intr (cprop_of case_hyp))
    |> map (fold_rev Thm.forall_intr cqs)
    |> map (Thm.close_derivation) 
  end
*}

ML {*
fun mk_uniqueness_clause thy globals compat_store eqvts clausei clausej RLj =
  let
    val Globals {h, y, x, fvar, ...} = globals
    val ClauseInfo {no=i, cdata=cctxi as ClauseContext {ctxt=ctxti, lhs=lhsi, case_hyp, cqs = cqsi, 
      ags = agsi, ...}, ...} = clausei
    val ClauseInfo {no=j, qglr=cdescj, RCs=RCsj, ...} = clausej

    val cctxj as ClauseContext {ags = agsj', lhs = lhsj', rhs = rhsj', qs = qsj', cqs = cqsj', ...} =
      mk_clause_context x ctxti cdescj 

    val rhsj'h = Pattern.rewrite_term thy [(fvar,h)] [] rhsj'

    val Ghsj' = map 
      (fn RCInfo {h_assum, ...} => Thm.assume (cterm_of thy (subst_bounds (rev qsj', h_assum)))) RCsj

    val y_eq_rhsj'h = Thm.assume (cterm_of thy (HOLogic.mk_Trueprop (mk_eq (y, rhsj'h))))
    val lhsi_eq_lhsj' = Thm.assume (cterm_of thy (HOLogic.mk_Trueprop (mk_eq (lhsi, lhsj'))))
       (* lhs_i = lhs_j' |-- lhs_i = lhs_j' *) 

    val case_hypj' = trans OF [case_hyp, lhsi_eq_lhsj']

    val RLj_import = RLj
      |> fold Thm.forall_elim cqsj'
      |> fold Thm.elim_implies agsj'
      |> fold Thm.elim_implies Ghsj'

    val eqvtsi = nth eqvts (i - 1)
      |> map (fold Thm.forall_elim cqsi)
      |> map (fold Thm.elim_implies [case_hyp])
      |> map (fold Thm.elim_implies agsi)

    val eqvtsj = nth eqvts (j - 1)
      |> map (fold Thm.forall_elim cqsj')
      |> map (fold Thm.elim_implies [case_hypj'])
      |> map (fold Thm.elim_implies agsj')

    val compat = get_compat_thm thy compat_store eqvtsi eqvtsj i j cctxi cctxj

  in
    (trans OF [case_hyp, lhsi_eq_lhsj']) (* lhs_i = lhs_j' |-- x = lhs_j' *)
    |> Thm.implies_elim RLj_import
      (* Rj1' ... Rjk', lhs_i = lhs_j' |-- rhs_j'_h = rhs_j'_f *)
    |> (fn it => trans OF [it, compat])
      (* lhs_i = lhs_j', Gj', Rj1' ... Rjk' |-- rhs_j'_h = rhs_i_f *)
    |> (fn it => trans OF [y_eq_rhsj'h, it])
      (* lhs_i = lhs_j', Gj', Rj1' ... Rjk', y = rhs_j_h' |-- y = rhs_i_f *)
    |> fold_rev (Thm.implies_intr o cprop_of) Ghsj'
    |> fold_rev (Thm.implies_intr o cprop_of) agsj'
      (* lhs_i = lhs_j' , y = rhs_j_h' |-- Gj', Rj1'...Rjk' ==> y = rhs_i_f *)
    |> Thm.implies_intr (cprop_of y_eq_rhsj'h)
    |> Thm.implies_intr (cprop_of lhsi_eq_lhsj')
    |> fold_rev Thm.forall_intr (cterm_of thy h :: cqsj')
  end
*}


ML {*
fun mk_uniqueness_case thy globals G f ihyp ih_intro G_cases compat_store clauses replems eqvtlems clausei =
  let
    val Globals {x, y, ranT, fvar, ...} = globals
    val ClauseInfo {cdata = ClauseContext {lhs, rhs, cqs, ags, case_hyp, ...}, lGI, RCs, ...} = clausei
    val rhsC = Pattern.rewrite_term thy [(fvar, f)] [] rhs

    val ih_intro_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ih_intro

    fun prep_RC (RCInfo {llRI, RIvs, CCas, ...}) = 
        (llRI RS ih_intro_case)
        |> fold_rev (Thm.implies_intr o cprop_of) CCas
        |> fold_rev (Thm.forall_intr o cterm_of thy o Free) RIvs

    val existence = fold (curry op COMP o prep_RC) RCs lGI

    val P = cterm_of thy (mk_eq (y, rhsC))
    val G_lhs_y = Thm.assume (cterm_of thy (HOLogic.mk_Trueprop (G $ lhs $ y)))

    val unique_clauses =
      map2 (mk_uniqueness_clause thy globals compat_store eqvtlems clausei) clauses replems

    fun elim_implies_eta A AB =
      Thm.compose_no_flatten true (A, 0) 1 AB |> Seq.list_of |> the_single

    val uniqueness = G_cases
      |> Thm.forall_elim (cterm_of thy lhs)
      |> Thm.forall_elim (cterm_of thy y)
      |> Thm.forall_elim P
      |> Thm.elim_implies G_lhs_y
      |> fold elim_implies_eta unique_clauses
      |> Thm.implies_intr (cprop_of G_lhs_y)
      |> Thm.forall_intr (cterm_of thy y)

    val P2 = cterm_of thy (lambda y (G $ lhs $ y)) (* P2 y := (lhs, y): G *)

    val exactly_one =
      ex1I |> instantiate' [SOME (ctyp_of thy ranT)] [SOME P2, SOME (cterm_of thy rhsC)]
      |> curry (op COMP) existence
      |> curry (op COMP) uniqueness
      |> simplify (HOL_basic_ss addsimps [case_hyp RS sym])
      |> Thm.implies_intr (cprop_of case_hyp)
      |> fold_rev (Thm.implies_intr o cprop_of) ags
      |> fold_rev Thm.forall_intr cqs

    val function_value =
      existence
      |> Thm.implies_intr ihyp
      |> Thm.implies_intr (cprop_of case_hyp)
      |> Thm.forall_intr (cterm_of thy x)
      |> Thm.forall_elim (cterm_of thy lhs)
      |> curry (op RS) refl
  in
    (exactly_one, function_value)
  end
*}


ML {*
fun prove_stuff ctxt globals G f R clauses complete compat compat_store G_elim G_eqvt f_def =
  let
    val Globals {h, domT, ranT, x, ...} = globals
    val thy = ProofContext.theory_of ctxt

    (* Inductive Hypothesis: !!z. (z,x):R ==> EX!y. (z,y):G *)
    val ihyp = Term.all domT $ Abs ("z", domT,
      Logic.mk_implies (HOLogic.mk_Trueprop (R $ Bound 0 $ x),
        HOLogic.mk_Trueprop (Const (@{const_name Ex1}, (ranT --> boolT) --> boolT) $
          Abs ("y", ranT, G $ Bound 1 $ Bound 0))))
      |> cterm_of thy

    val ihyp_thm = Thm.assume ihyp |> Thm.forall_elim_vars 0
    val ih_intro = ihyp_thm RS (f_def RS ex1_implies_ex)
    val ih_elim = ihyp_thm RS (f_def RS ex1_implies_un)
      |> instantiate' [] [NONE, SOME (cterm_of thy h)]
    val ih_eqvt = ihyp_thm RS (G_eqvt RS (f_def RS @{thm fundef_ex1_eqvt_at}))

    val _ = trace_msg (K "Proving Replacement lemmas...")
    val repLemmas = map (mk_replacement_lemma thy h ih_elim) clauses

    val _ = trace_msg (K "Proving Equivariance lemmas...")
    val eqvtLemmas = map (mk_eqvt_lemma thy ih_eqvt) clauses

    val _ = trace_msg (K "Proving cases for unique existence...")
    val (ex1s, values) =
      split_list (map (mk_uniqueness_case thy globals G f 
        ihyp ih_intro G_elim compat_store clauses repLemmas eqvtLemmas) clauses)
     
    val _ = trace_msg (K "Proving: Graph is a function")
    val graph_is_function = complete
      |> Thm.forall_elim_vars 0
      |> fold (curry op COMP) ex1s
      |> Thm.implies_intr (ihyp)
      |> Thm.implies_intr (cterm_of thy (HOLogic.mk_Trueprop (mk_acc domT R $ x)))
      |> Thm.forall_intr (cterm_of thy x)
      |> (fn it => Drule.compose_single (it, 2, acc_induct_rule)) (* "EX! y. (?x,y):G" *)
      |> (fn it => fold (Thm.forall_intr o cterm_of thy o Var) (Term.add_vars (prop_of it) []) it)

    val goalstate =  Conjunction.intr graph_is_function complete
      |> Thm.close_derivation
      |> Goal.protect
      |> fold_rev (Thm.implies_intr o cprop_of) compat
      |> Thm.implies_intr (cprop_of complete)
  in
    (goalstate, values)
  end
*}


ML {*
(* wrapper -- restores quantifiers in rule specifications *)
fun inductive_def eqvt_flag (binding as ((R, T), _)) intrs lthy =
  let
    val ({intrs = intrs_gen, elims = [elim_gen], preds = [ Rdef ], induct, raw_induct, ...}, lthy) =
      lthy
      |> Local_Theory.conceal 
      |> Inductive.add_inductive_i
          {quiet_mode = true,
            verbose = ! trace,
            alt_name = Binding.empty,
            coind = false,
            no_elim = false,
            no_ind = false,
            skip_mono = true,
            fork_mono = false}
          [binding] (* relation *)
          [] (* no parameters *)
          (map (fn t => (Attrib.empty_binding, t)) intrs) (* intro rules *)
          [] (* no special monos *)
      ||> Local_Theory.restore_naming lthy

    val eqvt_thm' = 
      if eqvt_flag = false then NONE
      else 
        let
          val ([eqvt_thm], lthy) = Nominal_Eqvt.raw_equivariance false [Rdef] raw_induct intrs_gen lthy
        in
          SOME ((Nominal_ThmDecls.eqvt_transform lthy eqvt_thm) RS @{thm eqvtI})
        end

    val cert = cterm_of (ProofContext.theory_of lthy)
    fun requantify orig_intro thm =
      let
        val (qs, t) = dest_all_all orig_intro
        val frees = frees_in_term lthy t |> remove (op =) (Binding.name_of R, T)
        val vars = Term.add_vars (prop_of thm) [] |> rev
        val varmap = AList.lookup (op =) (frees ~~ map fst vars)
          #> the_default ("",0)
      in
        fold_rev (fn Free (n, T) =>
          forall_intr_rename (n, cert (Var (varmap (n, T), T)))) qs thm
      end
  in
    ((Rdef, map2 requantify intrs intrs_gen, forall_intr_vars elim_gen, induct, eqvt_thm'), lthy)
  end
*}

ML {*
fun define_graph Gname fvar domT ranT clauses RCss lthy =
  let
    val GT = domT --> ranT --> boolT
    val (Gvar as (n, T)) = singleton (Variable.variant_frees lthy []) (Gname, GT)

    fun mk_GIntro (ClauseContext {qs, gs, lhs, rhs, ...}) RCs =
      let
        fun mk_h_assm (rcfix, rcassm, rcarg) =
          HOLogic.mk_Trueprop (Free Gvar $ rcarg $ (fvar $ rcarg))
          |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
          |> fold_rev (Logic.all o Free) rcfix
      in
        HOLogic.mk_Trueprop (Free Gvar $ lhs $ rhs)
        |> fold_rev (curry Logic.mk_implies o mk_h_assm) RCs
        |> fold_rev (curry Logic.mk_implies) gs
        |> fold_rev Logic.all (fvar :: qs)
      end

    val G_intros = map2 mk_GIntro clauses RCss
  in
    inductive_def true ((Binding.name n, T), NoSyn) G_intros lthy
  end
*}

ML {*
fun define_function fdefname (fname, mixfix) domT ranT G default lthy =
  let
    val f_def =
      Abs ("x", domT, Const (@{const_name FunDef.THE_default}, ranT --> (ranT --> boolT) --> ranT) 
        $ (default $ Bound 0) $ Abs ("y", ranT, G $ Bound 1 $ Bound 0))
      |> Syntax.check_term lthy
  in
    Local_Theory.define
      ((Binding.name (function_name fname), mixfix),
        ((Binding.conceal (Binding.name fdefname), []), f_def)) lthy
  end

fun define_recursion_relation Rname domT qglrs clauses RCss lthy =
  let
    val RT = domT --> domT --> boolT
    val (Rvar as (n, T)) = singleton (Variable.variant_frees lthy []) (Rname, RT)

    fun mk_RIntro (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) (rcfix, rcassm, rcarg) =
      HOLogic.mk_Trueprop (Free Rvar $ rcarg $ lhs)
      |> fold_rev (curry Logic.mk_implies o prop_of) rcassm
      |> fold_rev (curry Logic.mk_implies) gs
      |> fold_rev (Logic.all o Free) rcfix
      |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
      (* "!!qs xs. CS ==> G => (r, lhs) : R" *)

    val R_intross = map2 (map o mk_RIntro) (clauses ~~ qglrs) RCss

    val ((R, RIntro_thms, R_elim, _, _), lthy) =
      inductive_def false ((Binding.name n, T), NoSyn) (flat R_intross) lthy
  in
    ((R, Library.unflat R_intross RIntro_thms, R_elim), lthy)
  end


fun fix_globals domT ranT fvar ctxt =
  let
    val ([h, y, x, z, a, D, P, Pbool],ctxt') = Variable.variant_fixes
      ["h_fd", "y_fd", "x_fd", "z_fd", "a_fd", "D_fd", "P_fd", "Pb_fd"] ctxt
  in
    (Globals {h = Free (h, domT --> ranT),
      y = Free (y, ranT),
      x = Free (x, domT),
      z = Free (z, domT),
      a = Free (a, domT),
      D = Free (D, domT --> boolT),
      P = Free (P, domT --> boolT),
      Pbool = Free (Pbool, boolT),
      fvar = fvar,
      domT = domT,
      ranT = ranT},
    ctxt')
  end

fun inst_RC thy fvar f (rcfix, rcassm, rcarg) =
  let
    fun inst_term t = subst_bound(f, abstract_over (fvar, t))
  in
    (rcfix, map (Thm.assume o cterm_of thy o inst_term o prop_of) rcassm, inst_term rcarg)
  end



(**********************************************************
 *                   PROVING THE RULES
 **********************************************************)

fun mk_psimps thy globals R clauses valthms f_iff graph_is_function =
  let
    val Globals {domT, z, ...} = globals

    fun mk_psimp (ClauseInfo {qglr = (oqs, _, _, _), cdata = ClauseContext {cqs, lhs, ags, ...}, ...}) valthm =
      let
        val lhs_acc = cterm_of thy (HOLogic.mk_Trueprop (mk_acc domT R $ lhs)) (* "acc R lhs" *)
        val z_smaller = cterm_of thy (HOLogic.mk_Trueprop (R $ z $ lhs)) (* "R z lhs" *)
      in
        ((Thm.assume z_smaller) RS ((Thm.assume lhs_acc) RS acc_downward))
        |> (fn it => it COMP graph_is_function)
        |> Thm.implies_intr z_smaller
        |> Thm.forall_intr (cterm_of thy z)
        |> (fn it => it COMP valthm)
        |> Thm.implies_intr lhs_acc
        |> asm_simplify (HOL_basic_ss addsimps [f_iff])
        |> fold_rev (Thm.implies_intr o cprop_of) ags
        |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
      end
  in
    map2 mk_psimp clauses valthms
  end


(** Induction rule **)


val acc_subset_induct = @{thm predicate1I} RS @{thm accp_subset_induct}


fun mk_partial_induct_rule thy globals R complete_thm clauses =
  let
    val Globals {domT, x, z, a, P, D, ...} = globals
    val acc_R = mk_acc domT R

    val x_D = Thm.assume (cterm_of thy (HOLogic.mk_Trueprop (D $ x)))
    val a_D = cterm_of thy (HOLogic.mk_Trueprop (D $ a))

    val D_subset = cterm_of thy (Logic.all x
      (Logic.mk_implies (HOLogic.mk_Trueprop (D $ x), HOLogic.mk_Trueprop (acc_R $ x))))

    val D_dcl = (* "!!x z. [| x: D; (z,x):R |] ==> z:D" *)
      Logic.all x (Logic.all z (Logic.mk_implies (HOLogic.mk_Trueprop (D $ x),
        Logic.mk_implies (HOLogic.mk_Trueprop (R $ z $ x),
          HOLogic.mk_Trueprop (D $ z)))))
      |> cterm_of thy

    (* Inductive Hypothesis: !!z. (z,x):R ==> P z *)
    val ihyp = Term.all domT $ Abs ("z", domT,
      Logic.mk_implies (HOLogic.mk_Trueprop (R $ Bound 0 $ x),
        HOLogic.mk_Trueprop (P $ Bound 0)))
      |> cterm_of thy

    val aihyp = Thm.assume ihyp

    fun prove_case clause =
      let
        val ClauseInfo {cdata = ClauseContext {ctxt, qs, cqs, ags, gs, lhs, case_hyp, ...},
          RCs, qglr = (oqs, _, _, _), ...} = clause

        val case_hyp_conv = K (case_hyp RS eq_reflection)
        local open Conv in
          val lhs_D = fconv_rule (arg_conv (arg_conv (case_hyp_conv))) x_D
          val sih =
            fconv_rule (Conv.binder_conv
              (K (arg1_conv (arg_conv (arg_conv case_hyp_conv)))) ctxt) aihyp
        end

        fun mk_Prec (RCInfo {llRI, RIvs, CCas, rcarg, ...}) = sih
          |> Thm.forall_elim (cterm_of thy rcarg)
          |> Thm.elim_implies llRI
          |> fold_rev (Thm.implies_intr o cprop_of) CCas
          |> fold_rev (Thm.forall_intr o cterm_of thy o Free) RIvs

        val P_recs = map mk_Prec RCs   (*  [P rec1, P rec2, ... ]  *)

        val step = HOLogic.mk_Trueprop (P $ lhs)
          |> fold_rev (curry Logic.mk_implies o prop_of) P_recs
          |> fold_rev (curry Logic.mk_implies) gs
          |> curry Logic.mk_implies (HOLogic.mk_Trueprop (D $ lhs))
          |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
          |> cterm_of thy

        val P_lhs = Thm.assume step
          |> fold Thm.forall_elim cqs
          |> Thm.elim_implies lhs_D
          |> fold Thm.elim_implies ags
          |> fold Thm.elim_implies P_recs

        val res = cterm_of thy (HOLogic.mk_Trueprop (P $ x))
          |> Conv.arg_conv (Conv.arg_conv case_hyp_conv)
          |> Thm.symmetric (* P lhs == P x *)
          |> (fn eql => Thm.equal_elim eql P_lhs) (* "P x" *)
          |> Thm.implies_intr (cprop_of case_hyp)
          |> fold_rev (Thm.implies_intr o cprop_of) ags
          |> fold_rev Thm.forall_intr cqs
      in
        (res, step)
      end

    val (cases, steps) = split_list (map prove_case clauses)

    val istep = complete_thm
      |> Thm.forall_elim_vars 0
      |> fold (curry op COMP) cases (*  P x  *)
      |> Thm.implies_intr ihyp
      |> Thm.implies_intr (cprop_of x_D)
      |> Thm.forall_intr (cterm_of thy x)

    val subset_induct_rule =
      acc_subset_induct
      |> (curry op COMP) (Thm.assume D_subset)
      |> (curry op COMP) (Thm.assume D_dcl)
      |> (curry op COMP) (Thm.assume a_D)
      |> (curry op COMP) istep
      |> fold_rev Thm.implies_intr steps
      |> Thm.implies_intr a_D
      |> Thm.implies_intr D_dcl
      |> Thm.implies_intr D_subset

    val simple_induct_rule =
      subset_induct_rule
      |> Thm.forall_intr (cterm_of thy D)
      |> Thm.forall_elim (cterm_of thy acc_R)
      |> assume_tac 1 |> Seq.hd
      |> (curry op COMP) (acc_downward
        |> (instantiate' [SOME (ctyp_of thy domT)]
             (map (SOME o cterm_of thy) [R, x, z]))
        |> Thm.forall_intr (cterm_of thy z)
        |> Thm.forall_intr (cterm_of thy x))
      |> Thm.forall_intr (cterm_of thy a)
      |> Thm.forall_intr (cterm_of thy P)
  in
    simple_induct_rule
  end


(* FIXME: broken by design *)
fun mk_domain_intro ctxt (Globals {domT, ...}) R R_cases clause =
  let
    val thy = ProofContext.theory_of ctxt
    val ClauseInfo {cdata = ClauseContext {gs, lhs, cqs, ...},
      qglr = (oqs, _, _, _), ...} = clause
    val goal = HOLogic.mk_Trueprop (mk_acc domT R $ lhs)
      |> fold_rev (curry Logic.mk_implies) gs
      |> cterm_of thy
  in
    Goal.init goal
    |> (SINGLE (resolve_tac [accI] 1)) |> the
    |> (SINGLE (eresolve_tac [Thm.forall_elim_vars 0 R_cases] 1))  |> the
    |> (SINGLE (auto_tac (clasimpset_of ctxt))) |> the
    |> Goal.conclude
    |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
  end



(** Termination rule **)

val wf_induct_rule = @{thm Wellfounded.wfP_induct_rule}
val wf_in_rel = @{thm FunDef.wf_in_rel}
val in_rel_def = @{thm FunDef.in_rel_def}

fun mk_nest_term_case thy globals R' ihyp clause =
  let
    val Globals {z, ...} = globals
    val ClauseInfo {cdata = ClauseContext {qs, cqs, ags, lhs, case_hyp, ...}, tree,
      qglr=(oqs, _, _, _), ...} = clause

    val ih_case = full_simplify (HOL_basic_ss addsimps [case_hyp]) ihyp

    fun step (fixes, assumes) (_ $ arg) u (sub,(hyps,thms)) =
      let
        val used = (u @ sub)
          |> map (fn (ctx,thm) => Function_Ctx_Tree.export_thm thy ctx thm)

        val hyp = HOLogic.mk_Trueprop (R' $ arg $ lhs)
          |> fold_rev (curry Logic.mk_implies o prop_of) used (* additional hyps *)
          |> Function_Ctx_Tree.export_term (fixes, assumes)
          |> fold_rev (curry Logic.mk_implies o prop_of) ags
          |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
          |> cterm_of thy

        val thm = Thm.assume hyp
          |> fold Thm.forall_elim cqs
          |> fold Thm.elim_implies ags
          |> Function_Ctx_Tree.import_thm thy (fixes, assumes)
          |> fold Thm.elim_implies used (*  "(arg, lhs) : R'"  *)

        val z_eq_arg = HOLogic.mk_Trueprop (mk_eq (z, arg))
          |> cterm_of thy |> Thm.assume

        val acc = thm COMP ih_case
        val z_acc_local = acc
          |> Conv.fconv_rule
              (Conv.arg_conv (Conv.arg_conv (K (Thm.symmetric (z_eq_arg RS eq_reflection)))))

        val ethm = z_acc_local
          |> Function_Ctx_Tree.export_thm thy (fixes,
               z_eq_arg :: case_hyp :: ags @ assumes)
          |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)

        val sub' = sub @ [(([],[]), acc)]
      in
        (sub', (hyp :: hyps, ethm :: thms))
      end
      | step _ _ _ _ = raise Match
  in
    Function_Ctx_Tree.traverse_tree step tree
  end


fun mk_nest_term_rule thy globals R R_cases clauses =
  let
    val Globals { domT, x, z, ... } = globals
    val acc_R = mk_acc domT R

    val R' = Free ("R", fastype_of R)

    val Rrel = Free ("R", HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT)))
    val inrel_R = Const (@{const_name FunDef.in_rel},
      HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT)) --> fastype_of R) $ Rrel

    val wfR' = HOLogic.mk_Trueprop (Const (@{const_name Wellfounded.wfP},
      (domT --> domT --> boolT) --> boolT) $ R')
      |> cterm_of thy (* "wf R'" *)

    (* Inductive Hypothesis: !!z. (z,x):R' ==> z : acc R *)
    val ihyp = Term.all domT $ Abs ("z", domT,
      Logic.mk_implies (HOLogic.mk_Trueprop (R' $ Bound 0 $ x),
        HOLogic.mk_Trueprop (acc_R $ Bound 0)))
      |> cterm_of thy

    val ihyp_a = Thm.assume ihyp |> Thm.forall_elim_vars 0

    val R_z_x = cterm_of thy (HOLogic.mk_Trueprop (R $ z $ x))

    val (hyps, cases) = fold (mk_nest_term_case thy globals R' ihyp_a) clauses ([], [])
  in
    R_cases
    |> Thm.forall_elim (cterm_of thy z)
    |> Thm.forall_elim (cterm_of thy x)
    |> Thm.forall_elim (cterm_of thy (acc_R $ z))
    |> curry op COMP (Thm.assume R_z_x)
    |> fold_rev (curry op COMP) cases
    |> Thm.implies_intr R_z_x
    |> Thm.forall_intr (cterm_of thy z)
    |> (fn it => it COMP accI)
    |> Thm.implies_intr ihyp
    |> Thm.forall_intr (cterm_of thy x)
    |> (fn it => Drule.compose_single(it,2,wf_induct_rule))
    |> curry op RS (Thm.assume wfR')
    |> forall_intr_vars
    |> (fn it => it COMP allI)
    |> fold Thm.implies_intr hyps
    |> Thm.implies_intr wfR'
    |> Thm.forall_intr (cterm_of thy R')
    |> Thm.forall_elim (cterm_of thy (inrel_R))
    |> curry op RS wf_in_rel
    |> full_simplify (HOL_basic_ss addsimps [in_rel_def])
    |> Thm.forall_intr (cterm_of thy Rrel)
  end



(* Tail recursion (probably very fragile)
 *
 * FIXME:
 * - Need to do forall_elim_vars on psimps: Unneccesary, if psimps would be taken from the same context.
 * - Must we really replace the fvar by f here?
 * - Splitting is not configured automatically: Problems with case?
 *)
fun mk_trsimps octxt globals f G R f_def R_cases G_induct clauses psimps =
  let
    val Globals {domT, ranT, fvar, ...} = globals

    val R_cases = Thm.forall_elim_vars 0 R_cases (* FIXME: Should be already in standard form. *)

    val graph_implies_dom = (* "G ?x ?y ==> dom ?x"  *)
      Goal.prove octxt ["x", "y"] [HOLogic.mk_Trueprop (G $ Free ("x", domT) $ Free ("y", ranT))]
        (HOLogic.mk_Trueprop (mk_acc domT R $ Free ("x", domT)))
        (fn {prems=[a], ...} =>
          ((rtac (G_induct OF [a]))
          THEN_ALL_NEW rtac accI
          THEN_ALL_NEW etac R_cases
          THEN_ALL_NEW asm_full_simp_tac (simpset_of octxt)) 1)

    val default_thm =
      forall_intr_vars graph_implies_dom COMP (f_def COMP fundef_default_value)

    fun mk_trsimp clause psimp =
      let
        val ClauseInfo {qglr = (oqs, _, _, _), cdata =
          ClauseContext {ctxt, cqs, gs, lhs, rhs, ...}, ...} = clause
        val thy = ProofContext.theory_of ctxt
        val rhs_f = Pattern.rewrite_term thy [(fvar, f)] [] rhs

        val trsimp = Logic.list_implies(gs,
          HOLogic.mk_Trueprop (HOLogic.mk_eq(f $ lhs, rhs_f))) (* "f lhs = rhs" *)
        val lhs_acc = (mk_acc domT R $ lhs) (* "acc R lhs" *)
        fun simp_default_tac ss =
          asm_full_simp_tac (ss addsimps [default_thm, Let_def])
      in
        Goal.prove ctxt [] [] trsimp (fn _ =>
          rtac (instantiate' [] [SOME (cterm_of thy lhs_acc)] case_split) 1
          THEN (rtac (Thm.forall_elim_vars 0 psimp) THEN_ALL_NEW assume_tac) 1
          THEN (simp_default_tac (simpset_of ctxt) 1)
          THEN TRY ((etac not_acc_down 1)
            THEN ((etac R_cases)
              THEN_ALL_NEW (simp_default_tac (simpset_of ctxt))) 1))
        |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
      end
  in
    map2 mk_trsimp clauses psimps
  end
*}

ML {*
fun prepare_function config defname [((fname, fT), mixfix)] abstract_qglrs lthy =
  let
    val FunctionConfig {domintros, tailrec, default=default_opt, ...} = config

    val default_str = the_default "%x. undefined" default_opt (*FIXME dynamic scoping*)
    val fvar = Free (fname, fT)
    val domT = domain_type fT
    val ranT = range_type fT

    val default = Syntax.parse_term lthy default_str
      |> Type.constraint fT |> Syntax.check_term lthy

    val (globals, ctxt') = fix_globals domT ranT fvar lthy

    val Globals { x, h, ... } = globals

    val clauses = map (mk_clause_context x ctxt') abstract_qglrs

    val n = length abstract_qglrs

    fun build_tree (ClauseContext { ctxt, rhs, ...}) =
       Function_Ctx_Tree.mk_tree (fname, fT) h ctxt rhs

    val trees = map build_tree clauses
    val RCss = map find_calls trees

    val ((G, GIntro_thms, G_elim, G_induct, SOME G_eqvt), lthy) =
      PROFILE "def_graph" (define_graph (graph_name defname) fvar domT ranT clauses RCss) lthy

    val ((f, (_, f_defthm)), lthy) =
      PROFILE "def_fun" (define_function (defname ^ "_sumC_def") (fname, mixfix) domT ranT G default) lthy

    val RCss = map (map (inst_RC (ProofContext.theory_of lthy) fvar f)) RCss
    val trees = map (Function_Ctx_Tree.inst_tree (ProofContext.theory_of lthy) fvar f) trees

    val ((R, RIntro_thmss, R_elim), lthy) =
      PROFILE "def_rel" (define_recursion_relation (rel_name defname) domT abstract_qglrs clauses RCss) lthy

    val (_, lthy) =
      Local_Theory.abbrev Syntax.mode_default ((Binding.name (dom_name defname), NoSyn), mk_acc domT R) lthy

    val newthy = ProofContext.theory_of lthy
    val clauses = map (transfer_clause_ctx newthy) clauses

    val cert = cterm_of (ProofContext.theory_of lthy)

    val xclauses = PROFILE "xclauses"
      (map7 (mk_clause_info globals G f) (1 upto n) clauses abstract_qglrs trees
        RCss GIntro_thms) RIntro_thmss

    val complete =
      mk_completeness globals clauses abstract_qglrs |> cert |> Thm.assume

    val compat =
      mk_compat_proof_obligations domT ranT fvar f abstract_qglrs 
      |> map (cert #> Thm.assume)

    val compat_store = store_compat_thms n compat

    val (goalstate, values) = PROFILE "prove_stuff"
      (prove_stuff lthy globals G f R xclauses complete compat
         compat_store G_elim G_eqvt) f_defthm
     
    val mk_trsimps =
      mk_trsimps lthy globals f G R f_defthm R_elim G_induct xclauses

    fun mk_partial_rules provedgoal =
      let
        val newthy = theory_of_thm provedgoal (*FIXME*)

        val (graph_is_function, complete_thm) =
          provedgoal
          |> Conjunction.elim
          |> apfst (Thm.forall_elim_vars 0)

        val f_iff = graph_is_function RS (f_defthm RS ex1_implies_iff)

        val psimps = PROFILE "Proving simplification rules"
          (mk_psimps newthy globals R xclauses values f_iff) graph_is_function

        val simple_pinduct = PROFILE "Proving partial induction rule"
          (mk_partial_induct_rule newthy globals R complete_thm) xclauses

        val total_intro = PROFILE "Proving nested termination rule"
          (mk_nest_term_rule newthy globals R R_elim) xclauses

        val dom_intros =
          if domintros then SOME (PROFILE "Proving domain introduction rules"
             (map (mk_domain_intro lthy globals R R_elim)) xclauses)
           else NONE
        val trsimps = if tailrec then SOME (mk_trsimps psimps) else NONE

      in
        FunctionResult {fs=[f], G=G, R=R, cases=complete_thm,
          psimps=psimps, simple_pinducts=[simple_pinduct],
          termination=total_intro, trsimps=trsimps,
          domintros=dom_intros}
      end
  in
    ((f, goalstate, mk_partial_rules), lthy)
  end
*}

ML {*
open Function_Lib
open Function_Common

type qgar = string * (string * typ) list * term list * term list * term

datatype mutual_part = MutualPart of
 {i : int,
  i' : int,
  fvar : string * typ,
  cargTs: typ list,
  f_def: term,

  f: term option,
  f_defthm : thm option}

datatype mutual_info = Mutual of
 {n : int,
  n' : int,
  fsum_var : string * typ,

  ST: typ,
  RST: typ,

  parts: mutual_part list,
  fqgars: qgar list,
  qglrs: ((string * typ) list * term list * term * term) list,

  fsum : term option}

fun mutual_induct_Pnames n =
  if n < 5 then fst (chop n ["P","Q","R","S"])
  else map (fn i => "P" ^ string_of_int i) (1 upto n)

fun get_part fname =
  the o find_first (fn (MutualPart {fvar=(n,_), ...}) => n = fname)

(* FIXME *)
fun mk_prod_abs e (t1, t2) =
  let
    val bTs = rev (map snd e)
    val T1 = fastype_of1 (bTs, t1)
    val T2 = fastype_of1 (bTs, t2)
  in
    HOLogic.pair_const T1 T2 $ t1 $ t2
  end

fun analyze_eqs ctxt defname fs eqs =
  let
    val num = length fs
    val fqgars = map (split_def ctxt (K true)) eqs
    val arity_of = map (fn (fname,_,_,args,_) => (fname, length args)) fqgars
      |> AList.lookup (op =) #> the

    fun curried_types (fname, fT) =
      let
        val (caTs, uaTs) = chop (arity_of fname) (binder_types fT)
      in
        (caTs, uaTs ---> body_type fT)
      end

    val (caTss, resultTs) = split_list (map curried_types fs)
    val argTs = map (foldr1 HOLogic.mk_prodT) caTss

    val dresultTs = distinct (op =) resultTs
    val n' = length dresultTs

    val RST = Balanced_Tree.make (uncurry SumTree.mk_sumT) dresultTs
    val ST = Balanced_Tree.make (uncurry SumTree.mk_sumT) argTs

    val fsum_type = ST --> RST

    val ([fsum_var_name], _) = Variable.add_fixes [ defname ^ "_sum" ] ctxt
    val fsum_var = (fsum_var_name, fsum_type)

    fun define (fvar as (n, _)) caTs resultT i =
      let
        val vars = map_index (fn (j,T) => Free ("x" ^ string_of_int j, T)) caTs (* FIXME: Bind xs properly *)
        val i' = find_index (fn Ta => Ta = resultT) dresultTs + 1

        val f_exp = SumTree.mk_proj RST n' i' 
          (Free fsum_var $ SumTree.mk_inj ST num i (foldr1 HOLogic.mk_prod vars))
        
        val def = Term.abstract_over (Free fsum_var, fold_rev lambda vars f_exp)

        val rew = (n, fold_rev lambda vars f_exp)
      in
        (MutualPart {i=i, i'=i', fvar=fvar,cargTs=caTs,f_def=def,f=NONE,f_defthm=NONE}, rew)
      end

    val (parts, rews) = split_list (map4 define fs caTss resultTs (1 upto num))

    fun convert_eqs (f, qs, gs, args, rhs) =
      let
        val MutualPart {i, i', ...} = get_part f parts
      in
        (qs, gs, SumTree.mk_inj ST num i (foldr1 (mk_prod_abs qs) args),
         SumTree.mk_inj RST n' i' (replace_frees rews rhs)
         |> Envir.beta_norm)
      end

    val qglrs = map convert_eqs fqgars
  in
    Mutual {n=num, n'=n', fsum_var=fsum_var, ST=ST, RST=RST,
      parts=parts, fqgars=fqgars, qglrs=qglrs, fsum=NONE}
  end
*}

ML {*
fun define_projections fixes mutual fsum lthy =
  let
    fun def ((MutualPart {i=i, i'=i', fvar=(fname, fT), cargTs, f_def, ...}), (_, mixfix)) lthy =
      let
        val ((f, (_, f_defthm)), lthy') =
          Local_Theory.define
            ((Binding.name fname, mixfix),
              ((Binding.conceal (Binding.name (fname ^ "_def")), []),
              Term.subst_bound (fsum, f_def))) lthy
      in
        (MutualPart {i=i, i'=i', fvar=(fname, fT), cargTs=cargTs, f_def=f_def,
           f=SOME f, f_defthm=SOME f_defthm },
         lthy')
      end

    val Mutual { n, n', fsum_var, ST, RST, parts, fqgars, qglrs, ... } = mutual
    val (parts', lthy') = fold_map def (parts ~~ fixes) lthy
  in
    (Mutual { n=n, n'=n', fsum_var=fsum_var, ST=ST, RST=RST, parts=parts',
       fqgars=fqgars, qglrs=qglrs, fsum=SOME fsum },
     lthy')
  end

fun in_context ctxt (f, pre_qs, pre_gs, pre_args, pre_rhs) F =
  let
    val thy = ProofContext.theory_of ctxt

    val oqnames = map fst pre_qs
    val (qs, _) = Variable.variant_fixes oqnames ctxt
      |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs

    fun inst t = subst_bounds (rev qs, t)
    val gs = map inst pre_gs
    val args = map inst pre_args
    val rhs = inst pre_rhs

    val cqs = map (cterm_of thy) qs
    val ags = map (Thm.assume o cterm_of thy) gs

    val import = fold Thm.forall_elim cqs
      #> fold Thm.elim_implies ags

    val export = fold_rev (Thm.implies_intr o cprop_of) ags
      #> fold_rev forall_intr_rename (oqnames ~~ cqs)
  in
    F ctxt (f, qs, gs, args, rhs) import export
  end

fun recover_mutual_psimp all_orig_fdefs parts ctxt (fname, _, _, args, rhs)
  import (export : thm -> thm) sum_psimp_eq =
  let
    val (MutualPart {f=SOME f, ...}) = get_part fname parts

    val psimp = import sum_psimp_eq
    val (simp, restore_cond) =
      case cprems_of psimp of
        [] => (psimp, I)
      | [cond] => (Thm.implies_elim psimp (Thm.assume cond), Thm.implies_intr cond)
      | _ => raise General.Fail "Too many conditions"

  in
    Goal.prove ctxt [] []
      (HOLogic.Trueprop $ HOLogic.mk_eq (list_comb (f, args), rhs))
      (fn _ => (Local_Defs.unfold_tac ctxt all_orig_fdefs)
         THEN EqSubst.eqsubst_tac ctxt [0] [simp] 1
         THEN (simp_tac (simpset_of ctxt)) 1) (* FIXME: global simpset?!! *)
    |> restore_cond
    |> export
  end

fun mk_applied_form ctxt caTs thm =
  let
    val thy = ProofContext.theory_of ctxt
    val xs = map_index (fn (i,T) => cterm_of thy (Free ("x" ^ string_of_int i, T))) caTs (* FIXME: Bind xs properly *)
  in
    fold (fn x => fn thm => Thm.combination thm (Thm.reflexive x)) xs thm
    |> Conv.fconv_rule (Thm.beta_conversion true)
    |> fold_rev Thm.forall_intr xs
    |> Thm.forall_elim_vars 0
  end

fun mutual_induct_rules lthy induct all_f_defs (Mutual {n, ST, parts, ...}) =
  let
    val cert = cterm_of (ProofContext.theory_of lthy)
    val newPs =
      map2 (fn Pname => fn MutualPart {cargTs, ...} =>
          Free (Pname, cargTs ---> HOLogic.boolT))
        (mutual_induct_Pnames (length parts)) parts

    fun mk_P (MutualPart {cargTs, ...}) P =
      let
        val avars = map_index (fn (i,T) => Var (("a", i), T)) cargTs
        val atup = foldr1 HOLogic.mk_prod avars
      in
        HOLogic.tupled_lambda atup (list_comb (P, avars))
      end

    val Ps = map2 mk_P parts newPs
    val case_exp = SumTree.mk_sumcases HOLogic.boolT Ps

    val induct_inst =
      Thm.forall_elim (cert case_exp) induct
      |> full_simplify SumTree.sumcase_split_ss
      |> full_simplify (HOL_basic_ss addsimps all_f_defs)

    fun project rule (MutualPart {cargTs, i, ...}) k =
      let
        val afs = map_index (fn (j,T) => Free ("a" ^ string_of_int (j + k), T)) cargTs (* FIXME! *)
        val inj = SumTree.mk_inj ST n i (foldr1 HOLogic.mk_prod afs)
      in
        (rule
         |> Thm.forall_elim (cert inj)
         |> full_simplify SumTree.sumcase_split_ss
         |> fold_rev (Thm.forall_intr o cert) (afs @ newPs),
         k + length cargTs)
      end
  in
    fst (fold_map (project induct_inst) parts 0)
  end

fun mk_partial_rules_mutual lthy inner_cont (m as Mutual {parts, fqgars, ...}) proof =
  let
    val result = inner_cont proof
    val FunctionResult {G, R, cases, psimps, trsimps, simple_pinducts=[simple_pinduct],
      termination, domintros, ...} = result

    val (all_f_defs, fs) =
      map (fn MutualPart {f_defthm = SOME f_def, f = SOME f, cargTs, ...} =>
        (mk_applied_form lthy cargTs (Thm.symmetric f_def), f))
      parts
      |> split_list

    val all_orig_fdefs =
      map (fn MutualPart {f_defthm = SOME f_def, ...} => f_def) parts

    fun mk_mpsimp fqgar sum_psimp =
      in_context lthy fqgar (recover_mutual_psimp all_orig_fdefs parts) sum_psimp

    val rew_ss = HOL_basic_ss addsimps all_f_defs
    val mpsimps = map2 mk_mpsimp fqgars psimps
    val mtrsimps = Option.map (map2 mk_mpsimp fqgars) trsimps
    val minducts = mutual_induct_rules lthy simple_pinduct all_f_defs m
    val mtermination = full_simplify rew_ss termination
    val mdomintros = Option.map (map (full_simplify rew_ss)) domintros
  in
    FunctionResult { fs=fs, G=G, R=R,
      psimps=mpsimps, simple_pinducts=minducts,
      cases=cases, termination=mtermination,
      domintros=mdomintros, trsimps=mtrsimps}
  end

fun prepare_function_mutual config defname fixes eqss lthy =
  let
    val mutual as Mutual {fsum_var=(n, T), qglrs, ...} =
      analyze_eqs lthy defname (map fst fixes) (map Envir.beta_eta_contract eqss)

    val ((fsum, goalstate, cont), lthy') =
      prepare_function config defname [((n, T), NoSyn)] qglrs lthy

    val (mutual', lthy'') = define_projections fixes mutual fsum lthy'

    val mutual_cont = mk_partial_rules_mutual lthy'' cont mutual'
  in
    ((goalstate, mutual_cont), lthy'')
  end

*}


ML {*

open Function_Lib
open Function_Common

val simp_attribs = map (Attrib.internal o K)
  [Simplifier.simp_add,
   Code.add_default_eqn_attribute,
   Nitpick_Simps.add]

val psimp_attribs = map (Attrib.internal o K)
  [Nitpick_Psimps.add]

fun mk_defname fixes = fixes |> map (fst o fst) |> space_implode "_"

fun add_simps fnames post sort extra_qualify label mod_binding moreatts
  simps lthy =
  let
    val spec = post simps
      |> map (apfst (apsnd (fn ats => moreatts @ ats)))
      |> map (apfst (apfst extra_qualify))

    val (saved_spec_simps, lthy) =
      fold_map Local_Theory.note spec lthy

    val saved_simps = maps snd saved_spec_simps
    val simps_by_f = sort saved_simps

    fun add_for_f fname simps =
      Local_Theory.note
        ((mod_binding (Binding.qualify true fname (Binding.name label)), []), simps)
      #> snd
  in
    (saved_simps, fold2 add_for_f fnames simps_by_f lthy)
  end

fun prepare_function is_external prep default_constraint fixspec eqns config lthy =
  let
    val constrn_fxs = map (fn (b, T, mx) => (b, SOME (the_default default_constraint T), mx))
    val ((fixes0, spec0), ctxt') = prep (constrn_fxs fixspec) eqns lthy
    val fixes = map (apfst (apfst Binding.name_of)) fixes0;
    val spec = map (fn (bnd, prop) => (bnd, [prop])) spec0;
    val (eqs, post, sort_cont, cnames) = get_preproc lthy config ctxt' fixes spec

    val defname = mk_defname fixes
    val FunctionConfig {partials, tailrec, default, ...} = config
    val _ =
      if tailrec then Output.legacy_feature
        "'function (tailrec)' command. Use 'partial_function (tailrec)'."
      else ()
    val _ =
      if is_some default then Output.legacy_feature
        "'function (default)'. Use 'partial_function'."
      else ()

    val ((goal_state, cont), lthy') =
      prepare_function_mutual config defname fixes eqs lthy

    fun afterqed [[proof]] lthy =
      let
        val FunctionResult {fs, R, psimps, trsimps, simple_pinducts,
          termination, domintros, cases, ...} =
          cont (Thm.close_derivation proof)

        val fnames = map (fst o fst) fixes
        fun qualify n = Binding.name n
          |> Binding.qualify true defname
        val conceal_partial = if partials then I else Binding.conceal

        val addsmps = add_simps fnames post sort_cont

        val (((psimps', pinducts'), (_, [termination'])), lthy) =
          lthy
          |> addsmps (conceal_partial o Binding.qualify false "partial")
               "psimps" conceal_partial psimp_attribs psimps
          ||> (case trsimps of NONE => I | SOME thms =>
                   addsmps I "simps" I simp_attribs thms #> snd
                   #> Spec_Rules.add Spec_Rules.Equational (fs, thms))
          ||>> Local_Theory.note ((conceal_partial (qualify "pinduct"),
                 [Attrib.internal (K (Rule_Cases.case_names cnames)),
                  Attrib.internal (K (Rule_Cases.consumes 1)),
                  Attrib.internal (K (Induct.induct_pred ""))]), simple_pinducts)
          ||>> Local_Theory.note ((Binding.conceal (qualify "termination"), []), [termination])
          ||> (snd o Local_Theory.note ((qualify "cases",
                 [Attrib.internal (K (Rule_Cases.case_names cnames))]), [cases]))
          ||> (case domintros of NONE => I | SOME thms => 
                   Local_Theory.note ((qualify "domintros", []), thms) #> snd)

        val info = { add_simps=addsmps, case_names=cnames, psimps=psimps',
          pinducts=snd pinducts', simps=NONE, inducts=NONE, termination=termination',
          fs=fs, R=R, defname=defname, is_partial=true }

        val _ =
          if not is_external then ()
          else Specification.print_consts lthy (K false) (map fst fixes)
      in
        (info, 
         lthy |> Local_Theory.declaration false (add_function_data o morph_function_data info))
      end
  in
    ((goal_state, afterqed), lthy')
  end

*}

ML {*
fun gen_function is_external prep default_constraint fixspec eqns config lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_function is_external prep default_constraint fixspec eqns config lthy
  in
    lthy'
    |> Proof.theorem NONE (snd oo afterqed) [[(Logic.unprotect (concl_of goal_state), [])]]
    |> Proof.refine (Method.primitive_text (K goal_state)) 
    |> Seq.hd
  end
*}


ML {*
val function = gen_function false Specification.check_spec (Type_Infer.anyT HOLogic.typeS)
val function_cmd = gen_function true Specification.read_spec "_::type"

fun add_case_cong n thy =
  let
    val cong = #case_cong (Datatype.the_info thy n)
      |> safe_mk_meta_eq
  in
    Context.theory_map
      (Function_Ctx_Tree.map_function_congs (Thm.add_thm cong)) thy
  end

val setup_case_cong = Datatype.interpretation (K (fold add_case_cong))


(* setup *)

val setup =
  Attrib.setup @{binding fundef_cong}
    (Attrib.add_del Function_Ctx_Tree.cong_add Function_Ctx_Tree.cong_del)
    "declaration of congruence rule for function definitions"
  #> setup_case_cong
  #> Function_Relation.setup
  #> Function_Common.Termination_Simps.setup

val get_congs = Function_Ctx_Tree.get_function_congs

fun get_info ctxt t = Item_Net.retrieve (get_function ctxt) t
  |> the_single |> snd


(* outer syntax *)

val _ =
  Outer_Syntax.local_theory_to_proof "nominal_function" "define recursive functions for nominal types"
  Keyword.thy_goal
  (function_parser default_config
     >> (fn ((config, fixes), statements) => function_cmd fixes statements config))
*}

ML {* trace := true *}

lemma test:
  assumes a: "[[x]]lst. t = [[x]]lst. t'"
  shows "t = t'"
using a
apply(simp add: Abs_eq_iff)
apply(erule exE)
apply(simp only: alphas)
apply(erule conjE)+
apply(rule sym)
apply(clarify)
apply(rule supp_perm_eq)
apply(subgoal_tac "set [x] \<sharp>* p")
apply(auto simp add: fresh_star_def)[1]
apply(simp)
apply(simp add: fresh_star_def)
apply(simp add: fresh_perm)
done

lemma test2:
  assumes "a \<sharp> x" "c \<sharp> x" "b \<sharp> y" "c \<sharp> y"
  and "(a \<rightleftharpoons> c) \<bullet> x = (b \<rightleftharpoons> c) \<bullet> y"
  shows "x = y"
using assms by (simp add: swap_fresh_fresh)

lemma test3:
  assumes "x = y"
  and "a \<sharp> x" "c \<sharp> x" "b \<sharp> y" "c \<sharp> y"
  shows "(a \<rightleftharpoons> c) \<bullet> x = (b \<rightleftharpoons> c) \<bullet> y"
using assms by (simp add: swap_fresh_fresh)

nominal_function
  depth :: "lam \<Rightarrow> nat"
where
  "depth (Var x) = 1"
| "depth (App t1 t2) = (max (depth t1) (depth t2)) + 1"
| "depth (Lam x t) = (depth t) + 1"
apply(rule_tac y="x" in lam.exhaust)
apply(simp_all)[3]
apply(simp_all only: lam.distinct)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(subst (asm) Abs_eq_iff)
apply(erule exE)
apply(simp add: alphas)
apply(clarify)
oops

lemma removeAll_eqvt[eqvt]:
  shows "p \<bullet> (removeAll x xs) = removeAll (p \<bullet> x) (p \<bullet> xs)"
by (induct xs) (auto)

nominal_function 
  frees_lst :: "lam \<Rightarrow> atom list"
where
  "frees_lst (Var x) = [atom x]"
| "frees_lst (App t1 t2) = (frees_lst t1) @ (frees_lst t2)"
| "frees_lst (Lam x t) = removeAll (atom x) (frees_lst t)"
apply(rule_tac y="x" in lam.exhaust)
apply(simp_all)[3]
apply(simp_all only: lam.distinct)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: Abs_eq_iff)
apply(erule exE)
apply(simp add: alphas)
apply(simp add: atom_eqvt)
apply(clarify)
oops

nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [100,100,100] 100)
where
  "(Var x)[y ::= s] = (if x=y then s else (Var x))"
| "(App t\<^isub>1 t\<^isub>2)[y ::= s] = App (t\<^isub>1[y ::= s]) (t\<^isub>2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam x t)[y ::= s] = Lam x (t[y ::= s])"
apply(case_tac x)
apply(simp)
apply(rule_tac y="a" and c="(b, c)" in lam.strong_exhaust)
apply(simp add: lam.eq_iff lam.distinct)
apply(auto)[1]
apply(simp add: lam.eq_iff lam.distinct)
apply(auto)[1]
apply(simp add: fresh_star_def lam.eq_iff lam.distinct)
apply(simp_all add: lam.distinct)[5]
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(erule conjE)+
oops



nominal_function
  depth :: "lam \<Rightarrow> nat"
where
  "depth (Var x) = 1"
| "depth (App t1 t2) = (max (depth t1) (depth t2)) + 1"
| "depth (Lam x t) = (depth t) + 1"
apply(rule_tac y="x" in lam.exhaust)
apply(simp_all)[3]
apply(simp_all only: lam.distinct)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
(*
apply(subst (asm) Abs_eq_iff)
apply(erule exE)
apply(simp add: alphas)
apply(clarify)
*)
apply(subgoal_tac "finite (supp (x, xa, t, ta, depth_sumC t, depth_sumC ta))")
apply(erule_tac ?'a="name" in obtain_at_base)
unfolding fresh_def[symmetric]
apply(drule_tac a="atom x" and b="atom xa" and c="atom a" in test3)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(rule_tac a="atom x" and b="atom xa" and c="atom a" in test2)
apply(simp add: pure_fresh)
apply(simp add: pure_fresh)
apply(simp add: pure_fresh)
apply(simp add: pure_fresh)
apply(simp add: eqvt_at_def)
apply(drule test)
apply(simp)
apply(simp add: finite_supp)
done

termination depth
  apply(relation "measure size")
  apply(auto simp add: lam.size)
  done

thm depth.psimps
thm depth.simps


lemma swap_set_not_in_at:
  fixes a b::"'a::at"
  and   S::"'a::at set"
  assumes a: "a \<notin> S" "b \<notin> S"
  shows "(a \<leftrightarrow> b) \<bullet> S = S"
  unfolding permute_set_def
  using a by (auto simp add: permute_flip_at)

lemma removeAll_eqvt[eqvt]:
  shows "p \<bullet> (removeAll x xs) = removeAll (p \<bullet> x) (p \<bullet> xs)"
by (induct xs) (auto)

nominal_function 
  frees_lst :: "lam \<Rightarrow> atom list"
where
  "frees_lst (Var x) = [atom x]"
| "frees_lst (App t1 t2) = (frees_lst t1) @ (frees_lst t2)"
| "frees_lst (Lam x t) = removeAll (atom x) (frees_lst t)"
apply(rule_tac y="x" in lam.exhaust)
apply(simp_all)[3]
apply(simp_all only: lam.distinct)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: Abs_eq_iff)
apply(erule exE)
apply(simp add: alphas)
apply(simp add: atom_eqvt)
apply(clarify)
apply(rule trans)
apply(rule sym)
apply(rule_tac p="p" in supp_perm_eq)
oops

nominal_function 
  frees :: "lam \<Rightarrow> name set"
where
  "frees (Var x) = {x}"
| "frees (App t1 t2) = (frees t1) \<union> (frees t2)"
| "frees (Lam x t) = (frees t) - {x}"
apply(rule_tac y="x" in lam.exhaust)
apply(simp_all)[3]
apply(simp_all only: lam.distinct)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(subgoal_tac "finite (supp (x, xa, t, ta, frees_sumC t, frees_sumC ta))")
apply(erule_tac ?'a="name" in obtain_at_base)
unfolding fresh_def[symmetric]
apply(drule_tac a="atom x" and b="atom xa" and c="atom a" in test3)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp)
apply(drule test)
apply(rule_tac t="frees_sumC t - {x}" and s="(x \<leftrightarrow> a) \<bullet> (frees_sumC t - {x})" in subst)
oops

thm Abs_eq_iff[simplified alphas]

lemma Abs_set_eq_iff2:
  fixes x y::"'a::fs"
  shows "[bs]set. x = [cs]set. y \<longleftrightarrow>
    (\<exists>p. supp ([bs]set. x) = supp ([cs]set. y) \<and>
         supp ([bs]set. x) \<sharp>* p \<and>
         p \<bullet> x = y \<and> p \<bullet> bs = cs)"
unfolding Abs_eq_iff
unfolding alphas
unfolding supp_Abs
by simp

lemma Abs_set_eq_iff3:
  fixes x y::"'a::fs"
  assumes a: "finite bs" "finite cs"
  shows "[bs]set. x = [cs]set. y \<longleftrightarrow>
    (\<exists>p. supp ([bs]set. x) = supp ([cs]set. y) \<and>
         supp ([bs]set. x) \<sharp>* p \<and>
         p \<bullet> x = y \<and> p \<bullet> bs = cs \<and>
         supp p \<subseteq> bs \<union> cs)"
unfolding Abs_eq_iff
unfolding alphas
unfolding supp_Abs
apply(auto)
using set_renaming_perm
sorry

lemma Abs_eq_iff2:
  fixes x y::"'a::fs"
  shows "[bs]lst. x = [cs]lst. y \<longleftrightarrow>
    (\<exists>p. supp ([bs]lst. x) = supp ([cs]lst. y) \<and>
         supp ([bs]lst. x) \<sharp>* p \<and>
         p \<bullet> x = y \<and> p \<bullet> bs = cs)"
unfolding Abs_eq_iff
unfolding alphas
unfolding supp_Abs
by simp

lemma Abs_eq_iff3:
  fixes x y::"'a::fs"
  shows "[bs]lst. x = [cs]lst. y \<longleftrightarrow>
    (\<exists>p. supp ([bs]lst. x) = supp ([cs]lst. y) \<and>
         supp ([bs]lst. x) \<sharp>* p \<and>
         p \<bullet> x = y \<and> p \<bullet> bs = cs \<and>
         supp p \<subseteq> set bs \<union> set cs)"
unfolding Abs_eq_iff
unfolding alphas
unfolding supp_Abs
apply(auto)
using list_renaming_perm
apply -
apply(drule_tac x="bs" in meta_spec)
apply(drule_tac x="p" in meta_spec)
apply(erule exE)
apply(rule_tac x="q" in exI)
apply(simp add: set_eqvt)
sorry

nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [100,100,100] 100)
where
  "(Var x)[y ::= s] = (if x=y then s else (Var x))"
| "(App t\<^isub>1 t\<^isub>2)[y ::= s] = App (t\<^isub>1[y ::= s]) (t\<^isub>2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam x t)[y ::= s] = Lam x (t[y ::= s])"
apply(case_tac x)
apply(simp)
apply(rule_tac y="a" and c="(b, c)" in lam.strong_exhaust)
apply(simp add: lam.eq_iff lam.distinct)
apply(auto)[1]
apply(simp add: lam.eq_iff lam.distinct)
apply(auto)[1]
apply(simp add: fresh_star_def lam.eq_iff lam.distinct)
apply(simp_all add: lam.distinct)[5]
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(erule conjE)+
apply(subst (asm) Abs_eq_iff3) 
apply(erule exE)
apply(erule conjE)+
apply(clarify)
apply(perm_simp)
apply(simp)
apply(rule trans)
apply(rule sym)
apply(rule_tac p="p" in supp_perm_eq)
apply(rule fresh_star_supp_conv)
apply(drule fresh_star_supp_conv)
apply(simp add: Abs_fresh_star_iff)
thm fresh_eqvt_at
apply(rule_tac f="subst_sumC" in fresh_eqvt_at)
apply(assumption)
apply(simp add: finite_supp)
prefer 2
apply(simp)
apply(simp add: eqvt_at_def)
apply(perm_simp)
apply(subgoal_tac "p \<bullet> ya = ya")
apply(subgoal_tac "p \<bullet> sa = sa")
apply(simp)
apply(rule supp_perm_eq)
apply(rule fresh_star_supp_conv)
apply(auto simp add: fresh_star_def fresh_Pair)[1]
apply(rule supp_perm_eq)
apply(rule fresh_star_supp_conv)
apply(auto simp add: fresh_star_def fresh_Pair)[1]



nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [100,100,100] 100)
where
  "(Var x)[y ::= s] = (if x=y then s else (Var x))"
| "(App t\<^isub>1 t\<^isub>2)[y ::= s] = App (t\<^isub>1[y ::= s]) (t\<^isub>2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam x t)[y ::= s] = Lam x (t[y ::= s])"
apply(case_tac x)
apply(simp)
apply(rule_tac y="a" and c="(b, c)" in lam.strong_exhaust)
apply(simp add: lam.eq_iff lam.distinct)
apply(auto)[1]
apply(simp add: lam.eq_iff lam.distinct)
apply(auto)[1]
apply(simp add: fresh_star_def lam.eq_iff lam.distinct)
apply(simp_all add: lam.distinct)[5]
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(subgoal_tac "finite (supp (ya, sa, x, xa, t, ta, subst_sumC (t, ya, sa), subst_sumC (ta, ya, sa)))")
apply(erule_tac ?'a="name" in obtain_at_base)
unfolding fresh_def[symmetric]
apply(rule_tac a="atom x" and b="atom xa" and c="atom a" in test2)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(erule conjE)+
apply(drule_tac a="atom x" and b="atom xa" and c="atom a" in test3)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff)
apply(simp add: eqvt_at_def)
apply(drule test)
apply(simp)
apply(subst (2) swap_fresh_fresh)
apply(simp)
apply(simp)
apply(subst (2) swap_fresh_fresh)
apply(simp)
apply(simp)
apply(subst (3) swap_fresh_fresh)
apply(simp)
apply(simp)
apply(subst (3) swap_fresh_fresh)
apply(simp)
apply(simp)
apply(simp)
apply(simp add: finite_supp)
done

(* this should not work *)
nominal_function 
  bnds :: "lam \<Rightarrow> name set"
where
  "bnds (Var x) = {}"
| "bnds (App t1 t2) = (bnds t1) \<union> (bnds t2)"
| "bnds (Lam x t) = (bnds t) \<union> {x}"
apply(rule_tac y="x" in lam.exhaust)
apply(simp_all)[3]
apply(simp_all only: lam.distinct)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
apply(simp add: lam.eq_iff)
sorry

end



