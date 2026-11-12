(* PHI origins identify output variables, including distinct INVOKE outputs. *)
Theory phiOrigins
Ancestors
  phiDefs venomWf pred_set list

Definition get_origins_def:
  get_origins_list dfg (visited: num set) [] = {} /\
  get_origins_list dfg visited (v::vs) =
    (case dfg_lookup dfg v of
       NONE => v INSERT get_origins_list dfg visited vs
     | SOME src_inst =>
         get_origins dfg visited src_inst UNION get_origins_list dfg visited vs) /\

  get_origins dfg visited inst =
    if inst.inst_opcode = PHI then
      if inst.inst_id IN visited then
        {}
      else
        let visited' = inst.inst_id INSERT visited in
        let vars = phi_var_operands inst.inst_operands in
        let origins = get_origins_list dfg visited' vars in
        if CARD origins > 1 then set inst.inst_outputs
        else origins
    else if inst.inst_opcode = ASSIGN then
      case assign_var_operand inst of
        NONE => set inst.inst_outputs
      | SOME v =>
          if inst.inst_id IN visited then {}
          else
            let visited' = inst.inst_id INSERT visited in
            (case dfg_lookup dfg v of
               NONE => {v}
             | SOME src_inst => get_origins dfg visited' src_inst)
    else
      set inst.inst_outputs
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
           INL (dfg, visited, vars) =>
             (CARD (dfg_ids dfg DIFF visited), LENGTH vars)
         | INR (dfg, visited, inst) =>
             (CARD (dfg_ids dfg DIFF visited) +
                (if inst.inst_id IN dfg_ids dfg then 0 else 1), 0))` >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac dfg_lookup_implies_dfg_ids >> simp[] >>
  Cases_on `inst.inst_id IN dfg_ids dfg` >> simp[] >>
  TRY (irule CARD_PSUBSET >> simp[FINITE_DIFF, dfg_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
       qexists_tac `inst.inst_id` >> simp[] >> NO_TAC) >>
  TRY (`dfg_ids dfg DIFF (inst.inst_id INSERT visited) = dfg_ids dfg DIFF visited`
         by simp[DIFF_INSERT, DELETE_NON_ELEMENT_RWT] >> simp[] >> NO_TAC)
End

(* TOP-LEVEL: Main entry point for origin computation.
   Starts with empty visited set. *)
Definition compute_origins_def:
  compute_origins dfg inst = get_origins dfg {} inst
End

(* A multi-origin PHI is a barrier; a self-only PHI is left unchanged. *)
Definition phi_single_origin_def:
  phi_single_origin dfg inst =
    if ~is_phi_inst inst then NONE else
    case inst.inst_outputs of
      [out] =>
        let origins = compute_origins dfg inst in
        if CARD origins = 1 /\ out NOTIN origins
        then SOME (CHOICE origins) else NONE
    | _ => NONE
End

Theorem phi_single_origin_is_phi:
  !dfg inst origin.
    phi_single_origin dfg inst = SOME origin ==> is_phi_inst inst
Proof
  rw[phi_single_origin_def] >> gvs[AllCaseEqs()]
QED

(* Origin computation only combines finite collections of variables. *)
Theorem get_origins_finite:
  (!dfg visited vars. FINITE (get_origins_list dfg visited vars)) /\
  (!dfg visited inst. FINITE (get_origins dfg visited inst))
Proof
  ho_match_mp_tac get_origins_ind >>
  rpt strip_tac >> simp[Once get_origins_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem phi_single_origin_boundary:
  !dfg inst root.
    phi_single_origin dfg inst = SOME root ==>
    is_phi_inst inst /\
    ?out. inst.inst_outputs = [out] /\
          compute_origins dfg inst = {root} /\ root <> out
Proof
  rpt gen_tac >>
  simp[phi_single_origin_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `FINITE (compute_origins dfg inst)` by
    simp[compute_origins_def, get_origins_finite] >>
  `SING (compute_origins dfg inst)` by metis_tac[SING_IFF_CARD1] >>
  gvs[SING_DEF]
QED
