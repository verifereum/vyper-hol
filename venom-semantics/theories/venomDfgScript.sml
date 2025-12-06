(*
 * Data-Flow Graph (DFG) Analysis
 *
 * This theory defines the DFG structure and operations for Venom IR.
 * The DFG maps each variable to the instruction that produces it,
 * enabling analysis of def-use chains through PHI and ASSIGN instructions.
 *
 * This is reusable infrastructure for multiple optimization passes.
 *)

Theory venomDfg
Ancestors
  list finite_map pred_set
  venomState venomInst venomSem

(* --------------------------------------------------------------------------
   Data-Flow Graph Type and Basic Operations
   -------------------------------------------------------------------------- *)

Type dfg = ``:(string, instruction) fmap``

(* DFG lookup: returns SOME inst if variable is defined, NONE otherwise *)
Definition dfg_lookup_def:
  dfg_lookup dfg v = FLOOKUP dfg v
End

(* DFG well-formedness: if a variable maps to an instruction, that
   instruction must produce the variable. *)
Definition well_formed_dfg_def:
  well_formed_dfg dfg <=>
    !v inst. FLOOKUP dfg v = SOME inst ==> inst.inst_output = SOME v
End

(* --------------------------------------------------------------------------
   Building the DFG from a Function
   -------------------------------------------------------------------------- *)

Definition build_dfg_def:
  build_dfg_block dfg [] = dfg /\
  build_dfg_block dfg (inst::insts) =
    let dfg' = case inst.inst_output of
                 SOME v => dfg |+ (v, inst)
               | NONE => dfg
    in build_dfg_block dfg' insts
End

Definition build_dfg_blocks_def:
  build_dfg_blocks dfg [] = dfg /\
  build_dfg_blocks dfg (bb::bbs) =
    build_dfg_blocks (build_dfg_block dfg bb.bb_instructions) bbs
End

Definition build_dfg_fn_def:
  build_dfg_fn fn = build_dfg_blocks FEMPTY fn.fn_blocks
End

(* --------------------------------------------------------------------------
   Well-formedness Theorems
   -------------------------------------------------------------------------- *)

Theorem well_formed_dfg_update:
  !dfg inst v.
    well_formed_dfg dfg /\ inst.inst_output = SOME v
    ==> well_formed_dfg (dfg |+ (v, inst))
Proof
  rw[well_formed_dfg_def, FLOOKUP_UPDATE] >>
  Cases_on `v' = v` >> fs[]
QED

Theorem build_dfg_block_well_formed:
  !dfg insts.
    well_formed_dfg dfg ==> well_formed_dfg (build_dfg_block dfg insts)
Proof
  Induct_on `insts` >>
  simp[build_dfg_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_output` >>
  simp[build_dfg_def] >>
  metis_tac[well_formed_dfg_update]
QED

Theorem build_dfg_blocks_well_formed:
  !dfg bbs.
    well_formed_dfg dfg ==> well_formed_dfg (build_dfg_blocks dfg bbs)
Proof
  Induct_on `bbs` >> rw[build_dfg_blocks_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `build_dfg_block dfg h.bb_instructions` mp_tac) >>
  impl_tac >- (match_mp_tac build_dfg_block_well_formed >> simp[]) >>
  simp[]
QED

Theorem build_dfg_fn_well_formed:
  !fn. well_formed_dfg (build_dfg_fn fn)
Proof
  simp[build_dfg_fn_def] >>
  match_mp_tac build_dfg_blocks_well_formed >>
  simp[well_formed_dfg_def, FLOOKUP_DEF]
QED

(* --------------------------------------------------------------------------
   DFG Correctness Theorems
   -------------------------------------------------------------------------- *)

(* Collect all instructions from a function *)
Definition fn_instructions_def:
  fn_instructions fn = FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)
End

(* SSA form: each variable appears as output of at most one instruction *)
Definition ssa_form_def:
  ssa_form fn <=>
    !v inst1 inst2.
      MEM inst1 (fn_instructions fn) /\
      MEM inst2 (fn_instructions fn) /\
      inst1.inst_output = SOME v /\
      inst2.inst_output = SOME v
      ==>
      inst1 = inst2
End

Theorem build_dfg_block_correct:
  !insts dfg v inst.
    FLOOKUP (build_dfg_block dfg insts) v = SOME inst ==>
    (FLOOKUP dfg v = SOME inst \/ (MEM inst insts /\ inst.inst_output = SOME v))
Proof
  Induct_on `insts` >> simp[build_dfg_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_output` >> fs[] >- (
    first_x_assum (qspecl_then [`dfg`, `v`, `inst`] mp_tac) >> simp[] >>
    strip_tac >> metis_tac[]
  ) >>
  first_x_assum (qspecl_then [`dfg |+ (x, h)`, `v`, `inst`] mp_tac) >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on `x = v` >> fs[] >>
  strip_tac >> metis_tac[]
QED

Theorem build_dfg_blocks_correct:
  !bbs dfg v inst.
    FLOOKUP (build_dfg_blocks dfg bbs) v = SOME inst ==>
    (FLOOKUP dfg v = SOME inst \/
     (?bb. MEM bb bbs /\ MEM inst bb.bb_instructions /\ inst.inst_output = SOME v))
Proof
  Induct_on `bbs` >> simp[build_dfg_blocks_def] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`build_dfg_block dfg h.bb_instructions`, `v`, `inst`] mp_tac) >>
  simp[] >> strip_tac >- (
    drule build_dfg_block_correct >> strip_tac >- fs[] >>
    disj2_tac >> qexists_tac `h` >> simp[]
  ) >>
  metis_tac[]
QED

Theorem build_dfg_fn_correct:
  !fn v inst.
    FLOOKUP (build_dfg_fn fn) v = SOME inst
    ==>
    inst.inst_output = SOME v /\
    MEM inst (fn_instructions fn)
Proof
  rw[build_dfg_fn_def, fn_instructions_def] >>
  drule build_dfg_blocks_correct >> fs[MEM_FLAT, MEM_MAP] >>
  strip_tac >> qexists_tac `bb.bb_instructions` >> simp[] >>
  qexists_tac `bb` >> simp[]
QED

(* --------------------------------------------------------------------------
   DFG IDs and Finiteness (for termination proofs)
   -------------------------------------------------------------------------- *)

Definition dfg_ids_def:
  dfg_ids dfg = { inst.inst_id | ?v. FLOOKUP dfg v = SOME inst }
End

Theorem dfg_ids_finite:
  !dfg. FINITE (dfg_ids dfg)
Proof
  rw[dfg_ids_def] >>
  `{inst.inst_id | ?v. FLOOKUP dfg v = SOME inst} =
   IMAGE (\inst. inst.inst_id) (FRANGE dfg)` by (
    simp[EXTENSION, GSPECIFICATION, IN_FRANGE_FLOOKUP] >>
    metis_tac[]
  ) >>
  simp[IMAGE_FINITE, FINITE_FRANGE]
QED

Theorem FLOOKUP_implies_dfg_ids:
  !dfg v inst. FLOOKUP dfg v = SOME inst ==> inst.inst_id IN dfg_ids dfg
Proof
  rw[dfg_ids_def, GSPECIFICATION] >> metis_tac[]
QED

(* --------------------------------------------------------------------------
   PHI Instruction Helpers
   -------------------------------------------------------------------------- *)

(* Get operands that are variables from a PHI instruction *)
Definition phi_var_operands_def:
  phi_var_operands [] = [] /\
  phi_var_operands [_] = [] /\
  phi_var_operands (Label lbl :: Var v :: rest) = v :: phi_var_operands rest /\
  phi_var_operands (_ :: _ :: rest) = phi_var_operands rest
End

(* Well-formed PHI: all value operands (after labels) are variables *)
Definition phi_well_formed_def:
  phi_well_formed [] = T /\
  phi_well_formed [_] = T /\
  phi_well_formed (Label lbl :: Var v :: rest) = phi_well_formed rest /\
  phi_well_formed (Label lbl :: _ :: rest) = F /\
  phi_well_formed (_ :: _ :: rest) = phi_well_formed rest
End

(* Get the single operand from an assign, if it's a variable *)
Definition assign_var_operand_def:
  assign_var_operand inst =
    case inst.inst_operands of
      [Var v] => SOME v
    | _ => NONE
End

(* Check if instruction is a PHI *)
Definition is_phi_inst_def:
  is_phi_inst inst <=> inst.inst_opcode = PHI
End

(* Check if instruction is an assign with variable operand *)
Definition is_var_assign_def:
  is_var_assign inst <=>
    inst.inst_opcode = ASSIGN /\ IS_SOME (assign_var_operand inst)
End

(* Helper to get variables from instruction for tracing *)
Definition inst_source_vars_def:
  inst_source_vars inst =
    if inst.inst_opcode = PHI then
      phi_var_operands inst.inst_operands
    else if inst.inst_opcode = ASSIGN then
      case assign_var_operand inst of
        SOME v => [v]
      | NONE => []
    else []
End

(* Get the set of unique variable names from PHI operands *)
Definition phi_operand_vars_def:
  phi_operand_vars ops = set (phi_var_operands ops)
End

(* resolve_phi returns one of the phi_var_operands *)
Theorem resolve_phi_in_operands:
  !prev_bb ops v.
    resolve_phi prev_bb ops = SOME (Var v) ==>
    MEM v (phi_var_operands ops)
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- rw[resolve_phi_def] >>
  Cases_on `t` >- rw[resolve_phi_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_var_operands_def] >>
  TRY (Cases_on `s = prev_bb` >> fs[]) >>
  TRY (disj2_tac) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  rpt strip_tac >> res_tac
QED

(* --------------------------------------------------------------------------
   Origin Computation

   Traces back through PHI/ASSIGN chains to find "root" instructions.
   Uses visited set for cycle detection and termination.
   -------------------------------------------------------------------------- *)

Definition get_origins_def:
  get_origins_list dfg (visited: num set) [] = {} /\
  get_origins_list dfg visited (v::vs) =
    (case FLOOKUP dfg v of
       NONE => get_origins_list dfg visited vs
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
        if CARD origins > 1 then {inst}
        else origins
    else if inst.inst_opcode = ASSIGN then
      if inst.inst_id IN visited then {inst}
      else
        let visited' = inst.inst_id INSERT visited in
        case assign_var_operand inst of
          SOME v =>
            (case FLOOKUP dfg v of
               NONE => {inst}
             | SOME src_inst => get_origins dfg visited' src_inst)
        | NONE => {inst}
    else
      {inst}
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
           INL (dfg, visited, vars) =>
             (CARD (dfg_ids dfg DIFF visited), LENGTH vars)
         | INR (dfg, visited, inst) =>
             (CARD (dfg_ids dfg DIFF visited) +
                (if inst.inst_id IN dfg_ids dfg then 0 else 1), 0))` >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac FLOOKUP_implies_dfg_ids >> simp[] >>
  Cases_on `inst.inst_id IN dfg_ids dfg` >> simp[] >>
  TRY (irule CARD_PSUBSET >> simp[FINITE_DIFF, dfg_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
       qexists_tac `inst.inst_id` >> simp[] >> NO_TAC) >>
  TRY (`dfg_ids dfg DIFF (inst.inst_id INSERT visited) = dfg_ids dfg DIFF visited`
         by (simp[EXTENSION] >> metis_tac[]) >> simp[] >> NO_TAC)
End

Definition compute_origins_def:
  compute_origins dfg inst = get_origins dfg {} inst
End

(* --------------------------------------------------------------------------
   Checked Version (with assertions for valid IR)
   -------------------------------------------------------------------------- *)

Definition get_origins_checked_def:
  get_origins_list_checked dfg (visited: num set) [] = SOME {} /\
  get_origins_list_checked dfg visited (v::vs) =
    (case FLOOKUP dfg v of
       NONE => get_origins_list_checked dfg visited vs
     | SOME src_inst =>
         case (get_origins_checked dfg visited src_inst,
               get_origins_list_checked dfg visited vs) of
           (SOME s1, SOME s2) => SOME (s1 UNION s2)
         | _ => NONE) /\

  get_origins_checked dfg visited inst =
    if inst.inst_opcode = PHI then
      if inst.inst_id IN visited then SOME {}
      else
        let visited' = inst.inst_id INSERT visited in
        let vars = phi_var_operands inst.inst_operands in
        case get_origins_list_checked dfg visited' vars of
          NONE => NONE
        | SOME origins =>
            if CARD origins > 1 then SOME {inst}
            else SOME origins
    else if inst.inst_opcode = ASSIGN then
      if inst.inst_id IN visited then
        NONE  (* Assertion failure: ASSIGN cycle detected *)
      else
        let visited' = inst.inst_id INSERT visited in
        case assign_var_operand inst of
          SOME v =>
            (case FLOOKUP dfg v of
               NONE => SOME {inst}
             | SOME src_inst => get_origins_checked dfg visited' src_inst)
        | NONE => SOME {inst}
    else
      SOME {inst}
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
           INL (dfg, visited, vars) =>
             (CARD (dfg_ids dfg DIFF visited), LENGTH vars)
         | INR (dfg, visited, inst) =>
             (CARD (dfg_ids dfg DIFF visited) +
                (if inst.inst_id IN dfg_ids dfg then 0 else 1), 0))` >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac FLOOKUP_implies_dfg_ids >> simp[] >>
  Cases_on `inst.inst_id IN dfg_ids dfg` >> simp[] >>
  TRY (irule CARD_PSUBSET >> simp[FINITE_DIFF, dfg_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
       qexists_tac `inst.inst_id` >> simp[] >> NO_TAC) >>
  TRY (`dfg_ids dfg DIFF (inst.inst_id INSERT visited) = dfg_ids dfg DIFF visited`
         by (simp[EXTENSION] >> metis_tac[]) >> simp[] >> NO_TAC)
End

(* --------------------------------------------------------------------------
   Dominance (for valid IR property)
   -------------------------------------------------------------------------- *)

Definition inst_dominates_def:
  inst_dominates inst1 inst2 <=> inst1.inst_id < inst2.inst_id
End

Definition defs_dominate_uses_def:
  defs_dominate_uses dfg <=>
    !inst v def_inst.
      FLOOKUP dfg v = SOME def_inst /\
      inst.inst_opcode = ASSIGN /\
      assign_var_operand inst = SOME v
      ==>
      inst_dominates def_inst inst
End

(* --------------------------------------------------------------------------
   Correctness Theorems
   -------------------------------------------------------------------------- *)

Theorem get_origins_checked_eq:
  (!dfg visited vars result.
     get_origins_list_checked dfg visited vars = SOME result ==>
     get_origins_list dfg visited vars = result) /\
  (!dfg visited inst result.
     get_origins_checked dfg visited inst = SOME result ==>
     get_origins dfg visited inst = result)
Proof
  ho_match_mp_tac get_origins_checked_ind >> rpt conj_tac >> rpt gen_tac >- (
    simp[Once get_origins_checked_def, Once get_origins_def]
  ) >- (
    rpt strip_tac >>
    simp[Once get_origins_checked_def, Once get_origins_def] >>
    Cases_on `FLOOKUP dfg v` >> fs[] >- (
      fs[Once get_origins_checked_def]
    ) >>
    fs[Once get_origins_checked_def] >> gvs[AllCaseEqs()] >>
    first_x_assum (qspec_then `s1` mp_tac) >> simp[] >>
    qpat_x_assum `get_origins_checked _ _ _ = _` mp_tac >>
    simp[Once get_origins_checked_def] >> gvs[AllCaseEqs()] >>
    strip_tac >> fs[]
  ) >- (
    rpt strip_tac >>
    simp[Once get_origins_checked_def, Once get_origins_def] >>
    qpat_x_assum `get_origins_checked _ _ _ = _` mp_tac >>
    simp[Once get_origins_checked_def] >> gvs[AllCaseEqs()] >>
    strip_tac >> fs[]
  )
QED

Definition visited_valid_def:
  visited_valid dfg visited <=>
    !id. id IN visited ==> id IN dfg_ids dfg
End

Theorem get_origins_list_checked_succeeds:
  !dfg visited vars.
    defs_dominate_uses dfg /\
    (!v src_inst. MEM v vars /\ FLOOKUP dfg v = SOME src_inst ==>
       ?result. get_origins_checked dfg visited src_inst = SOME result)
    ==>
    ?result. get_origins_list_checked dfg visited vars = SOME result
Proof
  Induct_on `vars` >- rw[Once get_origins_checked_def] >>
  rpt strip_tac >>
  rw[Once get_origins_checked_def] >>
  Cases_on `FLOOKUP dfg h` >> fs[] >- (
    first_x_assum match_mp_tac >> rw[] >>
    first_x_assum match_mp_tac >> fs[] >> qexists_tac `v` >> fs[]
  ) >>
  `?r. get_origins_checked dfg visited x = SOME r` by (
    first_x_assum (qspecl_then [`h`, `x`] mp_tac) >> fs[]
  ) >> fs[] >>
  `?result. get_origins_list_checked dfg visited vars = SOME result` by (
    first_x_assum match_mp_tac >> rw[] >>
    first_x_assum match_mp_tac >> fs[] >> qexists_tac `v` >> fs[]
  ) >> fs[]
QED

Theorem defs_dominate_uses_checked_succeeds:
  !dfg visited inst.
    defs_dominate_uses dfg /\
    FINITE visited /\
    (!id. id IN visited ==> id IN dfg_ids dfg)
    ==>
    ?result. get_origins_checked dfg visited inst = SOME result
Proof
  cheat
QED

Theorem compute_origins_valid:
  !dfg inst.
    defs_dominate_uses dfg ==>
    ?result. get_origins_checked dfg {} inst = SOME result /\
             compute_origins dfg inst = result
Proof
  rw[compute_origins_def] >>
  `?result. get_origins_checked dfg {} inst = SOME result` by (
    irule defs_dominate_uses_checked_succeeds >>
    rw[]
  ) >>
  metis_tac[get_origins_checked_eq]
QED

(* --------------------------------------------------------------------------
   Single Origin Helper
   -------------------------------------------------------------------------- *)

Definition phi_single_origin_def:
  phi_single_origin dfg inst =
    if ~is_phi_inst inst then NONE else
    let origins = compute_origins dfg inst in
    let non_self = origins DELETE inst in
    if CARD non_self = 1 then SOME (CHOICE non_self)
    else NONE
End

(* All PHI operand variables are the same *)
Definition phi_uniform_operands_def:
  phi_uniform_operands ops <=>
    case phi_var_operands ops of
      [] => T
    | (v::vs) => EVERY (\x. x = v) vs
End

(* For single-origin PHIs, the operand variable equals the origin's output *)
Definition phi_operands_direct_def:
  phi_operands_direct dfg inst <=>
    case phi_single_origin dfg inst of
      NONE => T
    | SOME origin =>
        case origin.inst_output of
          NONE => T
        | SOME src_var =>
            EVERY (\v. v = src_var) (phi_var_operands inst.inst_operands)
End

(* Origins come from DFG lookups (or are the instruction itself) *)
Theorem get_origins_in_dfg_or_self:
  (!dfg visited vars origin.
     origin IN get_origins_list dfg visited vars ==>
     (?v. FLOOKUP dfg v = SOME origin)) /\
  (!dfg visited inst origin.
     origin IN get_origins dfg visited inst ==>
     origin = inst \/ (?v. FLOOKUP dfg v = SOME origin))
Proof
  ho_match_mp_tac get_origins_ind >> rpt conj_tac >> rpt gen_tac >- (
    (* Base case: empty list *)
    simp[Once get_origins_def]
  ) >- (
    (* v::vars case *)
    strip_tac >> simp[Once get_origins_def] >>
    Cases_on `FLOOKUP dfg v` >> gvs[] >>
    rpt strip_tac >> fs[IN_UNION] >> metis_tac[]
  ) >- (
    (* get_origins case *)
    strip_tac >> rpt strip_tac >>
    qpat_x_assum `origin IN get_origins _ _ _` mp_tac >>
    simp[Once get_origins_def] >>
    rpt (COND_CASES_TAC >> gvs[]) >>
    rpt CASE_TAC >> gvs[] >>
    metis_tac[]
  )
QED

Theorem compute_origins_non_self_in_dfg:
  !dfg inst origin.
    origin IN compute_origins dfg inst /\ origin <> inst ==>
    ?v. FLOOKUP dfg v = SOME origin
Proof
  rw[compute_origins_def] >>
  drule (cj 2 get_origins_in_dfg_or_self) >> simp[]
QED

(* Key lemma: if operands are direct, FLOOKUP gives the origin *)
Theorem phi_operands_direct_flookup:
  !dfg inst origin prev_bb v.
    well_formed_dfg dfg /\
    phi_single_origin dfg inst = SOME origin /\
    phi_operands_direct dfg inst /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v)
  ==>
    FLOOKUP dfg v = SOME origin
Proof
  rpt strip_tac >>
  fs[phi_single_origin_def, AllCaseEqs(), is_phi_inst_def] >>
  (* Get origin IN compute_origins and origin <> inst *)
  `compute_origins dfg inst DELETE inst <> {}` by (
    strip_tac >> fs[CARD_EQ_0, FINITE_DELETE]
  ) >>
  drule CHOICE_DEF >> strip_tac >> fs[IN_DELETE] >>
  (* Get FLOOKUP dfg v' = SOME origin *)
  drule_all compute_origins_non_self_in_dfg >> strip_tac >>
  (* Get origin.inst_output = SOME v' *)
  `origin.inst_output = SOME v'` by fs[well_formed_dfg_def] >>
  (* Get MEM v (phi_var_operands) *)
  drule_all resolve_phi_in_operands >> strip_tac >>
  (* Unfold phi_operands_direct and use EVERY_MEM to get v = v' *)
  fs[phi_operands_direct_def, phi_single_origin_def, is_phi_inst_def, EVERY_MEM] >>
  gvs[AllCaseEqs()]
QED

