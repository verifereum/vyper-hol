(*
 * PHI Elimination Well-Formedness Definitions
 *
 * This theory defines well-formedness conditions for PHI elimination.
 * wf_ir_fn is the syntactic condition users should check.
 * phi_wf_fn is the semantic condition used in proofs.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - wf_ir_fn             : Syntactic well-formedness for Venom IR
 *   - phi_wf_fn            : PHI-specific well-formedness conditions
 *
 * TOP-LEVEL THEOREMS:
 *   - wf_ir_implies_phi_wf : Syntactic WF implies PHI WF
 *
 * ============================================================================
 *)

Theory phiWellFormed
Ancestors
  phiTransform stateEquiv venomSem venomState dfgDefs dfgOrigins list

(* ==========================================================================
   Well-Formedness Definitions
   ========================================================================== *)

(* TOP-LEVEL: Simple syntactic well-formedness for Venom IR functions.
   Users should check this to ensure PHI elimination is correct. *)
Definition wf_ir_fn_def:
  wf_ir_fn func <=>
    (* SSA form: each variable defined at most once *)
    ssa_form func /\
    (* All PHI operands are well-formed (Label/Var pairs) *)
    (!bb idx inst.
       MEM bb func.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (* All PHI instructions have single output (required for well-formed PHI) *)
    (!bb idx inst.
       MEM bb func.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst ==>
       ?out. inst.inst_outputs = [out]) /\
    (* Entry block has no PHI instructions *)
    (func.fn_blocks <> [] ==>
       !idx inst. get_instruction (HD func.fn_blocks) idx = SOME inst ==>
                  ~is_phi_inst inst) /\
    (* For PHIs with single origin, operands directly use the origin's output *)
    (!bb idx inst.
       let dfg = dfg_build_function func in
       MEM bb func.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst ==>
       phi_operands_direct dfg inst) /\
    (* PHI operands cover all reachable predecessors - if PHI errors, it's from
       undefined operand not missing predecessor *)
    (!bb idx inst prev s e.
       MEM bb func.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst /\
       s.vs_prev_bb = SOME prev /\
       step_inst inst s = Error e ==>
       ?val_op. resolve_phi prev inst.inst_operands = SOME val_op)
End

(* Helper: Well-formedness predicate for a function's PHI instructions.
   This is the semantic condition used in the main correctness proofs. *)
Definition phi_wf_fn_def:
  phi_wf_fn func <=>
    (* All PHI instructions are well-formed *)
    (!bb idx inst.
       MEM bb func.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (* DFG origins are consistent with phi resolution - scoped to blocks
       Note: is_phi_inst is implied by phi_single_origin = SOME *)
    (!bb idx inst origin prev_bb v.
       let dfg = dfg_build_function func in
       MEM bb func.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       dfg_lookup dfg v = SOME origin) /\
    (* Entry block has no PHI instructions with single origin (crucial for correctness) *)
    (!idx inst.
       let dfg = dfg_build_function func in
       func.fn_blocks <> [] /\
       get_instruction (HD func.fn_blocks) idx = SOME inst ==>
       phi_single_origin dfg inst = NONE) /\
    (* For Error case: if PHI with single origin errors, origin's output undefined
       This holds in well-formed SSA due to dominator properties.
       Note: is_phi_inst is implied by phi_single_origin = SOME *)
    (!bb inst origin src_var prev e s.
       let dfg = dfg_build_function func in
       MEM bb func.fn_blocks /\
       get_instruction bb s.vs_inst_idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       origin.inst_outputs = [src_var] /\
       s.vs_prev_bb = SOME prev /\
       step_inst inst s = Error e ==>
       lookup_var src_var s = NONE)
End

(* ==========================================================================
   PHI Resolution Lemmas
   ========================================================================== *)

(* Note: resolve_phi_in_operands is in dfgDefsTheory *)

Theorem resolve_phi_well_formed:
  !prev_bb ops v.
    phi_well_formed ops /\
    resolve_phi prev_bb ops = SOME v ==>
    ?var. v = Var var
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- rw[resolve_phi_def] >>
  Cases_on `t` >- rw[resolve_phi_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_well_formed_def] >>
  TRY (Cases_on `s = prev_bb` >> fs[]) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  strip_tac >> res_tac >> metis_tac[]
QED

(* Helper: PHI instruction stepping in terms of resolve_phi and eval_operand *)
Theorem step_inst_phi_eval:
  !inst out prev s.
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev
  ==>
    step_inst inst s =
      case resolve_phi prev inst.inst_operands of
        NONE => Error "phi: no matching predecessor"
      | SOME val_op =>
          case eval_operand val_op s of
            SOME v => OK (update_var out v s)
          | NONE => Error "phi: undefined operand"
Proof
  rw[step_inst_def]
QED

(* ==========================================================================
   Main Theorem: Syntactic implies Semantic WF
   ========================================================================== *)

(* TOP-LEVEL: wf_ir_fn implies phi_wf_fn.
   This is the key theorem that allows users to check the simpler syntactic
   conditions (wf_ir_fn) and get the semantic guarantees (phi_wf_fn). *)
Theorem wf_ir_implies_phi_wf:
  !func. wf_ir_fn func ==> phi_wf_fn func
Proof
  rw[wf_ir_fn_def, phi_wf_fn_def, LET_DEF] >>
  rpt strip_tac
  >- (
    (* PHI well-formed operands - direct from wf_ir_fn *)
    metis_tac[]
  )
  >- (
    (* DFG origin lookup - use phi_operands_direct_lookup *)
    (* First derive is_phi_inst from phi_single_origin = SOME *)
    `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
    (* Then derive phi_operands_direct from wf_ir_fn assumption *)
    `phi_operands_direct (dfg_build_function func) inst` by (
      qpat_x_assum `!bb idx inst. _ ==> phi_operands_direct _ _`
        (qspecl_then [`bb`, `idx`, `inst`] mp_tac) >> simp[]
    ) >>
    irule phi_operands_direct_lookup >>
    qexists_tac `inst` >> qexists_tac `prev_bb` >> simp[]
  )
  >- (
    (* Entry block no PHI with single origin - follows from no PHIs at all *)
    fs[phi_single_origin_def, is_phi_inst_def] >>
    first_x_assum (qspecl_then [`idx`, `inst`] mp_tac) >> simp[]
  )
  >- (
    (* Error case: PHI with single origin errors implies origin undefined. *)
    (* Derive is_phi_inst from phi_single_origin = SOME *)
    `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
    fs[is_phi_inst_def] >>
    (* Get phi_well_formed from wf_ir_fn assumption *)
    `phi_well_formed inst.inst_operands` by (
      qpat_x_assum `!bb' idx inst'. _ ==> phi_well_formed _`
        (qspecl_then [`bb`, `s.vs_inst_idx`, `inst`] mp_tac) >> simp[]
    ) >>
    (* Get inst.inst_outputs = [out] from wf_ir_fn assumption *)
    `?out. inst.inst_outputs = [out]` by (
      qpat_x_assum `!bb' idx inst'. _ ==> ?out. inst'.inst_outputs = [out]`
        (qspecl_then [`bb`, `s.vs_inst_idx`, `inst`] mp_tac) >> simp[]
    ) >>
    (* Get resolve_phi success from wf_ir_fn's error condition *)
    `?val_op. resolve_phi prev inst.inst_operands = SOME val_op` by (
      qpat_x_assum `!bb' idx inst' prev' s' e'. _ ==> ?val_op. resolve_phi _ _ = SOME _`
        (qspecl_then [`bb`, `s.vs_inst_idx`, `inst`, `prev`, `s`, `e`] mp_tac) >> simp[]
    ) >>
    (* Get phi_operands_direct from wf_ir_fn assumption *)
    `phi_operands_direct (dfg_build_function func) inst` by (
      qpat_x_assum `!bb' idx inst'. _ ==> phi_operands_direct _ _`
        (qspecl_then [`bb`, `s.vs_inst_idx`, `inst`] mp_tac) >> simp[]
    ) >>
    gvs[] >>
    (* Use step_inst_phi_eval with explicit arguments *)
    qspecl_then [`inst`, `out`, `prev`, `s`] mp_tac step_inst_phi_eval >> simp[] >>
    strip_tac >> gvs[] >>
    Cases_on `eval_operand val_op s` >> gvs[AllCaseEqs()] >>
    (* val_op must be Var var since phi_well_formed *)
    `?var. val_op = Var var` by (
      qspecl_then [`prev`, `inst.inst_operands`, `val_op`] mp_tac resolve_phi_well_formed >>
      simp[]
    ) >>
    gvs[eval_operand_def] >>
    (* MEM var (phi_var_operands) via resolve_phi_in_operands *)
    `MEM var (phi_var_operands inst.inst_operands)` by (
      drule resolve_phi_in_operands >> simp[]
    ) >>
    (* Unfold phi_operands_direct with our known cases to get EVERY *)
    fs[phi_operands_direct_def] >> gvs[AllCaseEqs(), EVERY_MEM] >>
    (* Use EVERY_MEM to get var = src_var *)
    `var = src_var` by (
      first_x_assum (qspec_then `var` mp_tac) >> simp[]
    ) >>
    gvs[]
  )
QED
