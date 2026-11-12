(*
 * Return-PC variables under the frame view.
 *
 * frame_view fn ra substitutes ra for every return-PC variable.  Under
 * SSA and opaque_use_ok, an instruction other than a copy (ASSIGN, PHI)
 * or RET neither reads nor writes one, so its operands evaluate the same
 * through the view; ASSIGN copies one through it.
 *
 * TOP-LEVEL:
 *   ordinary_operand_not_retpc — non-copy operands are not return-PC vars
 *   noncopy_output_not_retpc   — non-copy outputs are not return-PC vars
 *   frame_view_update_var      — the view of a variable update
 *   eval_operand_frame_view    — non-return-PC operands read the same
 *   eval_operands_frame_view   — the same for operand lists
 *   assign_step_frame_view     — an ASSIGN step through the view
 *)

Theory frameViewFacts
Ancestors
  frameRel unitShapeDefs stackPlanGen allocaRemapSSA venomInst venomState
  finite_map list venomExecSemantics contextCodegenRel

Theorem retpc_var_output_cases:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ retpc_var fn x ==>
  inst.inst_opcode = RETPC_PARAM \/
  (?y. inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] /\
       retpc_var fn y) \/
  (?y. inst.inst_opcode = PHI /\ MEM (Var y) inst.inst_operands /\
       retpc_var fn y)
Proof
  strip_tac >>
  qpat_x_assum `retpc_var fn x` mp_tac >>
  simp[retpc_var_def, Once copy_phi_var_cases] >>
  strip_tac >> rename1 `MEM producer (fn_insts fn)` >>
  `inst = producer` by metis_tac[ssa_unique_output] >> gvs[] >>
  metis_tac[]
QED

Theorem noncopy_output_not_retpc:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode <> RETPC_PARAM /\ inst.inst_opcode <> ASSIGN /\
  inst.inst_opcode <> PHI ==> ~retpc_var fn x
Proof
  metis_tac[retpc_var_output_cases]
QED

Theorem assign_output_retpc:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] ==>
  (retpc_var fn x <=> retpc_var fn y)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> drule_all retpc_var_output_cases >> simp[])
  >> simp[retpc_var_def] >> strip_tac >>
  irule copy_phi_var_assign >> metis_tac[]
QED

(* Shape-level direction for PHI copies; independent of SSA uniqueness. *)
Theorem phi_retpc_output_input:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM out inst.inst_outputs /\ MEM (Var src) inst.inst_operands /\
  retpc_var fn out ==> retpc_var fn src
Proof
  strip_tac >>
  qpat_x_assum `retpc_shape_ok fn`
    (mp_tac o cj 3 o REWRITE_RULE [retpc_shape_ok_def]) >>
  disch_then drule_all >> simp[]
QED

Theorem phi_output_retpc:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM out inst.inst_outputs /\ MEM (Var src) inst.inst_operands ==>
  (retpc_var fn out <=> retpc_var fn src)
Proof
  strip_tac >> eq_tac
  >- metis_tac[phi_retpc_output_input] >>
  simp[retpc_var_def] >> metis_tac[copy_phi_var_phi]
QED

Theorem assign_nonvar_output_not_retpc:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  (!y. op <> Var y) ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >> drule_all retpc_var_output_cases >>
  simp[] >> metis_tac[]
QED

Theorem ordinary_operand_not_retpc:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM (Var x) inst.inst_operands /\ inst.inst_opcode <> ASSIGN /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> RET /\
  inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET ==>
  ~retpc_var fn x
Proof
  rpt strip_tac >> drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def]
QED

Theorem codegen_ready_inst_not_pre:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) ==>
  ~is_pre_codegen_opcode inst.inst_opcode
Proof
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)`
    by (Induct >> simp[fn_insts_blocks_def]) >>
  simp[codegen_ready_fn_def, fn_insts_def, MEM_FLAT, MEM_MAP,
       EVERY_MEM, codegen_ready_inst_def] >> metis_tac[]
QED

Theorem frame_view_update_var:
  frame_view fn ra (update_var x v s) =
  update_var x (if retpc_var fn x then ra else v) (frame_view fn ra s)
Proof
  simp[frame_view_def, update_var_def, FMAP_MAP2_FUPDATE]
QED

Theorem frame_view_memory:
  frame_view fn ra (s with vs_memory := m) =
  frame_view fn ra s with vs_memory := m
Proof
  simp[frame_view_def]
QED

Theorem eval_operand_frame_view:
  (!x. op = Var x ==> ~retpc_var fn x) ==>
  eval_operand op (frame_view fn ra s with vs_memory := m) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def,
    frame_view_def, FLOOKUP_FMAP_MAP2] >>
  strip_tac >> rename1 `FLOOKUP s.vs_vars x` >>
  Cases_on `FLOOKUP s.vs_vars x` >> simp[]
QED

Theorem eval_operands_frame_view:
  (!x. MEM (Var x) ops ==> ~retpc_var fn x) ==>
  eval_operands ops (frame_view fn ra s with vs_memory := m) =
  eval_operands ops s
Proof
  Induct_on `ops` >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h (frame_view fn ra s with vs_memory := m) =
   eval_operand h s` by (irule eval_operand_frame_view >> metis_tac[]) >>
  simp[]
QED

Theorem assign_eval_frame_view:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  MEM x inst.inst_outputs /\ eval_operand op s = SOME v ==>
  eval_operand op (frame_view fn ra s with vs_memory := m) =
  SOME (if retpc_var fn x then ra else v)
Proof
  strip_tac >> Cases_on `op`
  >- (`~retpc_var fn x` by
        (strip_tac >> drule_all retpc_var_output_cases >> simp[]) >>
      gvs[eval_operand_def, frame_view_def])
  >- (rename1 `eval_operand (Var y) s = SOME v` >>
      drule_all assign_output_retpc >> strip_tac >>
      gvs[eval_operand_def, lookup_var_def, frame_view_vars_lookup])
  >> `~retpc_var fn x` by
       (strip_tac >> drule_all retpc_var_output_cases >> simp[]) >>
     gvs[eval_operand_def, frame_view_def]
QED

Theorem assign_base_frame_view:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ step_inst_base inst s = OK s' ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `inst.inst_outputs = [x]` >>
  rename1 `eval_operand op s = SOME v` >>
  `eval_operand op (frame_view fn ra s with vs_memory := m) =
   SOME (if retpc_var fn x then ra else v)` by
    (irule assign_eval_frame_view >> simp[] >> qexists_tac `inst` >> simp[]) >>
  simp[Once step_inst_base_def] >>
  simp[frame_view_update_var, update_var_def, frame_view_def]
QED

Theorem assign_step_frame_view:
  step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ASSIGN /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) ==>
  ?m'. step_inst fuel ctx inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `step_inst_base inst s = OK s'` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
     simp[Once step_inst_def]) >>
  drule_all assign_base_frame_view >>
  disch_then (qspecl_then [`ra`, `m`] assume_tac) >>
  qexists_tac `m` >> conj_tac
  >- simp[Once step_inst_def]
  >> simp[] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def]
QED
