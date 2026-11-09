(* Same-path ghost transport probes, not compiler dominance assertions. *)
Theory augAssignPtrProvenancePath
Ancestors
  augAssignPtrScalarAudit augAssignPtrProvenanceProbe decoderGhostFramePtr
  fragGasPathPtr ptrSafeRun
  ptrDiscipline venomInst finite_map pred_set list

Theorem ghost_step_other_output:
  ~MEM x inst.inst_outputs ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = FLOOKUP G x
Proof
  strip_tac >> simp[Once ghost_step_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[]
  >- (Cases_on `decode_invoke inst` >> simp[] >>
      rename1 `decode_invoke inst = SOME call` >> PairCases_on `call` >>
      simp[] >> Cases_on `lookup_function call0 ctx.ctx_functions` >> simp[] >>
      Cases_on `eval_operands call1 s` >> simp[] >>
      rename1 `eval_operands call1 s = SOME args` >>
      rename1 `lookup_function call0 ctx.ctx_functions = SOME callee` >>
      Cases_on `setup_callee callee args s` >> simp[FLOOKUP_DRESTRICT]) >>
  Cases_on `step_inst fuel ctx inst s` >>
  simp[step_prov_other_output]
QED

Theorem gas_path_ptr_provenance_frame:
  !D lo ctx fn PG G tn s n H tm r.
    gas_path_ptr D lo ctx fn PG G tn s n H tm r ==>
    !x region.
      region s /\
      (!G0 tn0 s0 k G1 tn1 r0.
         region s0 /\
         gas_path_ptr_edge D lo ctx fn PG G0 tn0 s0 k G1 tn1 r0 ==>
         FLOOKUP G1 x = FLOOKUP G0 x /\
         (!t. r0 = OK t ==> region t)) ==>
      FLOOKUP H x = FLOOKUP G x
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt strip_tac >>
  metis_tac[]
QED

Theorem gas_path_ptr_untagged_frame:
  gas_path_ptr D lo ctx fn PG G tn s n H tm r /\
  op_prov G (Var x) = NONE /\ region s /\
  (!G0 tn0 s0 k G1 tn1 r0.
     region s0 /\ gas_path_ptr_edge D lo ctx fn PG G0 tn0 s0 k G1 tn1 r0 ==>
     FLOOKUP G1 x = FLOOKUP G0 x /\ (!t. r0 = OK t ==> region t)) ==>
  op_prov H (Var x) = NONE
Proof
  strip_tac >> drule gas_path_ptr_provenance_frame >>
  disch_then (qspecl_then [`x`, `region`] mp_tac) >> gvs[op_prov_def] >> metis_tac[]
QED

(* INVOKE does not copy callee variable provenance back into caller variables.
   It deletes exactly caller outputs; failure before setup leaves G unchanged. *)
Theorem invoke_output_has_no_provenance:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  MEM x inst.inst_outputs ==>
  op_prov (FST (ghost_step fuel ctx PG G tn inst s)) (Var x) = NONE
Proof
  strip_tac >> drule_all ghost_step_invoke >>
  disch_then assume_tac >> simp[op_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem load_then_preserving_path_untagged:
  MEM opc [MLOAD; SLOAD; TLOAD; CALLDATALOAD] /\
  gas_path_ptr D lo ctx fn PG
    (step_prov PG G (mk_inst id opc [src] [x]) u) tn s n H tm r /\
  region s /\
  (!G0 tn0 s0 k G1 tn1 r0.
     region s0 /\ gas_path_ptr_edge D lo ctx fn PG G0 tn0 s0 k G1 tn1 r0 ==>
     FLOOKUP G1 x = FLOOKUP G0 x /\ (!t. r0 = OK t ==> region t)) ==>
  op_prov H (Var x) = NONE
Proof
  strip_tac >>
  `op_prov (step_prov PG G (mk_inst id opc [src] [x]) u) (Var x) = NONE`
    by (irule load_result_has_no_provenance >> simp[]) >>
  metis_tac[gas_path_ptr_untagged_frame]
QED

Theorem load_ghost_result_has_no_provenance:
  MEM opc [MLOAD; SLOAD; TLOAD; CALLDATALOAD] /\
  step_inst fuel ctx (mk_inst id opc [src] [x]) s = OK u ==>
  op_prov (FST (ghost_step fuel ctx PG G tn (mk_inst id opc [src] [x]) s))
    (Var x) = NONE
Proof
  strip_tac >>
  `((mk_inst id opc [src] [x]).inst_opcode <> INVOKE)`
    by (gvs[MEM, mk_inst_def]) >>
  drule_all ghost_step_non_invoke >> disch_then assume_tac >>
  simp[load_result_has_no_provenance]
QED

(* The equality identifies the actual ghost of the clearing edge, rather than
   choosing an unrelated clean execution. region is a suffix invariant: using
   a condition on ALL edges of fn would also constrain the earlier clearing
   edge and can make the interface useless. *)
Theorem load_ghost_then_preserving_path_untagged:
  MEM opc [MLOAD; SLOAD; TLOAD; CALLDATALOAD] /\
  step_inst fuel ctx (mk_inst id opc [src] [x]) before = OK u /\
  ghost_step fuel ctx PG G tn0 (mk_inst id opc [src] [x]) before = (G1, tn) /\
  gas_path_ptr D lo ctx fn PG G1 tn s n H tm r /\ region s /\
  (!G0 tm0 s0 k G2 tm2 r0.
     region s0 /\ gas_path_ptr_edge D lo ctx fn PG G0 tm0 s0 k G2 tm2 r0 ==>
     FLOOKUP G2 x = FLOOKUP G0 x /\ (!t. r0 = OK t ==> region t)) ==>
  op_prov H (Var x) = NONE
Proof
  strip_tac >> drule_all load_ghost_result_has_no_provenance >>
  disch_then (qspecl_then [`tn0`, `PG`, `G`] mp_tac) >>
  simp[] >> strip_tac >>
  drule gas_path_ptr_provenance_frame >>
  disch_then (qspecl_then [`x`, `region`] mp_tac) >>
  gvs[op_prov_def] >> metis_tac[]
QED

(* Proposed compiler boundary, NOT asserted by the probes above:

   expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
   lower_value compile_expr cenv ty e sa = (op, sb) /\
   fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
   local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
   ~cenv.ce_is_ctor /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at sa x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at sa x) /\
   stmt_state_rel ctx func cenv cx es s0 /\
   ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
   s0.vs_current_bb = sa.cs_current_bb /\
   s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
   gas_path_ptr (cx_dead cx) (cx_tops cx) ctx func PG
                G0 tn0 s0 n G tn (OK t) /\
   expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts
   ==> op_prov G op = NONE

   All variables in this proposed statement are universally quantified. It
   refers to the SAME supplied path and its ghosts, not an existential new
   run. expr_body_pre carries typing/environment/width/call-safety assumptions
   (see augAssignPtrScalarAudit); body_inv and the body typing context may
   still be required to establish the internal-call declared-type boundary.

   Remaining proof obligations (no certification by this comment):
   - Definition dominance on this path: successful arrival at sb must pass a
     clearing definition, or recursively certified scalar forwarding. Static
     freshness and fn_inst_ids_distinct alone do not establish this.
   - Suffix region closure: account for every possible write to the result,
     including PHIs on block entry and loops/re-entry; ghost_step_other_output
     describes only the instruction transition, not an entire path edge.
   - Branch joins: IfExp/default-call joins ASSIGN one of the recursively
     clean scalar arms; prove the arm actually traversed on this same path.
   - Propagating ADD/SUB/ASSIGN and identity conversions require recursive
     operand cleanliness, not merely ptr_val_ok or empty taint.
   - Internal call metadata and type_widens_to must exclude a nonword declared
     return represented as a word annotation. External/default return paths
     also require ABI size and well-formed type facts. INVOKE clearing above
     does not by itself solve these compiler typing/dominance obligations.

   If arbitrary paths satisfying the endpoint post are too broad (e.g. after
   re-entry), the appropriate alternative is to strengthen the normal post
   of the gas_outcome_ptr witness furnished by expr_sim_ptr, retaining that
   witness's exact counted path. No such strengthening is proved here.
*)
