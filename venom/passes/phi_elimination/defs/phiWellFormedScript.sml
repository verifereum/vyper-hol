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
 *   - phi_elim_safe_fn     : No eliminated PHI reads a variable defined in the same block
 *
 * TOP-LEVEL THEOREMS:
 *   - wf_ir_implies_phi_wf : Syntactic WF implies PHI WF
 *
 * ============================================================================
 *)

Theory phiWellFormed
Ancestors
  phiTransform stateEquivProps venomExecSemantics venomState venomWf phiDefs phiOrigins list

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
    (* PHI operands cover all reachable predecessors - if eval_one_phi fails,
       it's from undefined operand not missing predecessor *)
    (!bb idx inst prev s.
       MEM bb func.fn_blocks /\
       get_instruction bb idx = SOME inst /\
       is_phi_inst inst /\
       s.vs_prev_bb = SOME prev /\
       eval_one_phi s inst = NONE ==>
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
    (* For eval_one_phi failure: if PHI with single origin fails, origin's output undefined
       This holds in well-formed SSA due to dominator properties.
       Note: is_phi_inst is implied by phi_single_origin = SOME *)
    (!bb inst origin src_var prev s.
       let dfg = dfg_build_function func in
       MEM bb func.fn_blocks /\
       get_instruction bb s.vs_inst_idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       origin.inst_outputs = [src_var] /\
       s.vs_prev_bb = SOME prev /\
       eval_one_phi s inst = NONE ==>
       lookup_var src_var s = NONE)
End

(* Additional semantic side condition needed by parallel PHI semantics.
   Python's PHI elimination can replace a single-origin PHI with an ASSIGN that
   executes after the PHI/PARAM prefix. That is sound only when the ASSIGN's
   source is not overwritten by any instruction in the same block before the
   ASSIGN executes. A simple block-local sufficient condition is that the source
   is not output by any instruction in the block. *)
Definition phi_elim_safe_fn_def:
  phi_elim_safe_fn func <=>
    let dfg = dfg_build_function func in
      !bb inst origin src_var.
        MEM bb func.fn_blocks /\
        MEM inst bb.bb_instructions /\
        phi_single_origin dfg inst = SOME origin /\
        origin.inst_outputs = [src_var]
        ==>
        !producer.
          MEM producer bb.bb_instructions ==>
          ~MEM src_var producer.inst_outputs
End

Theorem phi_elim_safe_fn_source_not_output:
  !func bb inst origin src_var producer.
    phi_elim_safe_fn func /\
    MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    phi_single_origin (dfg_build_function func) inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    MEM producer bb.bb_instructions ==>
    ~MEM src_var producer.inst_outputs
Proof
  rw[phi_elim_safe_fn_def, LET_DEF] >> metis_tac[]
QED

(* ==========================================================================
   PHI Resolution Lemmas
   ========================================================================== *)

(* Note: resolve_phi_in_operands is in phiDefsTheory *)

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

(* Helper: eval_one_phi in terms of resolve_phi and eval_operand *)
Theorem eval_one_phi_eq:
  !inst out prev s.
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev
  ==>
    eval_one_phi s inst =
      case resolve_phi prev inst.inst_operands of
        NONE => NONE
      | SOME val_op =>
          case eval_operand val_op s of
            SOME v => SOME (out, v)
          | NONE => NONE
Proof
  rw[eval_one_phi_def] >> simp[]
QED

(* After PHI semantics change, step_inst_base for PHI always errors *)
Theorem step_inst_base_phi_error:
  !inst s. inst.inst_opcode = PHI ==> step_inst_base inst s = Error "phi outside prefix"
Proof
  rw[step_inst_base_def]
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
    (* Derive is_phi_inst from phi_single_origin = SOME *)
    `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
    (* Derive phi_operands_direct from wf_ir_fn assumption *)
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
    (* eval_one_phi failure case: PHI with single origin fails implies origin undefined. *)
    (* Derive is_phi_inst from phi_single_origin = SOME *)
    `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
    fs[is_phi_inst_def] >>
    `phi_well_formed inst.inst_operands` by (
      qpat_x_assum `!bb' idx inst'. _ ==> phi_well_formed _`
        (qspecl_then [`bb`, `s.vs_inst_idx`, `inst`] mp_tac) >> simp[]
    ) >>
    `?out. inst.inst_outputs = [out]` by (
      qpat_x_assum `!bb' idx inst'. _ ==> ?out. inst'.inst_outputs = [out]`
        (qspecl_then [`bb`, `s.vs_inst_idx`, `inst`] mp_tac) >> simp[]
    ) >>
    `?val_op. resolve_phi prev inst.inst_operands = SOME val_op` by (
      qpat_x_assum `!bb' idx inst' prev' s'. _ ==> ?val_op. resolve_phi _ _ = SOME _`
        (qspecl_then [`bb`, `s.vs_inst_idx`, `inst`, `prev`, `s`] mp_tac) >> simp[]
    ) >>
    `phi_operands_direct (dfg_build_function func) inst` by (
      qpat_x_assum `!bb' idx inst'. _ ==> phi_operands_direct _ _`
        (qspecl_then [`bb`, `s.vs_inst_idx`, `inst`] mp_tac) >> simp[]
    ) >>
    gvs[] >>
    (* Use eval_one_phi_eq: eval_one_phi fails, but resolve_phi succeeded,
       so eval_operand must have returned NONE *)
    qspecl_then [`inst`, `out`, `prev`, `s`] mp_tac eval_one_phi_eq >> simp[] >>
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
