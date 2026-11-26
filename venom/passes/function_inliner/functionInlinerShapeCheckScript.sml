(* An executable check for the inliner's syntactic shape premise.
 *
 * TOP-LEVEL:
 *   o1_ctx_shape_check, o1_ctx_shape_check_sound
 *   inliner_shape_check, inliner_shape_check_sound
 *
 * The call-rank existential is checked against a rank the caller supplies.
 * PHI coverage has its own check (phis_cover_preds_check). Self-contained
 * revert-forwarding pairs, a conjunct of inliner_input_guard, are checked by
 * rfp_self_contained_check (rfp_self_contained_check_guard).
 * Definite assignment stays a premise: its executable check rejects PHIs.
 *)
Theory functionInlinerShapeCheck
Ancestors
  functionInlinerContract o1SourceUnitCheck defsReachCheck o1PassContract
  contextCodegenRel callLayoutDefs unitShapeDefs dretDesugarDefs fcgDefs
  venomWf venomInst list rich_list
Libs
  BasicProvers

(* ===== Pass-contract shape ===== *)

Definition o1_fn_shape_check_def:
  o1_fn_shape_check ctx fn <=>
    wf_function fn /\ EVERY inst_wf (fn_insts fn) /\
    fn_shape_check fn /\ first_block_no_preds fn /\ first_block_no_phi fn /\
    copy_phi_closed GAS fn (copy_phi_vars GAS fn) /\
    copy_phi_closed RETPC_PARAM fn (copy_phi_vars RETPC_PARAM fn) /\
    EVERY (\inst.
      (inst.inst_opcode = INVOKE ==>
         case inst.inst_operands of
           Label lbl :: rest => MEM lbl (ctx_fn_names ctx)
         | _ => F) /\
      (inst.inst_opcode <> INVOKE ==>
         EVERY (\op. case op of
                       Label l => MEM l (fn_labels fn) \/ reserved_label l
                     | _ => T) inst.inst_operands) /\
      inst.inst_opcode <> DRET /\
      (inst.inst_opcode = DALLOCA ==>
         EVERY (\x. ~MEM x (copy_phi_vars GAS fn) /\
                    ~MEM x (copy_phi_vars RETPC_PARAM fn))
           inst.inst_outputs))
      (fn_insts fn) /\
    (ctx.ctx_entry = SOME fn.fn_name ==>
       entry_fn_no_return fn /\ entry_fn_no_params fn) /\
    (ctx.ctx_entry <> SOME fn.fn_name ==>
       EVERY (\inst. ~MEM inst.inst_opcode [STOP; RETURN]) (fn_insts fn))
End

Theorem o1_fn_shape_check_sound:
  o1_fn_shape_check ctx fn ==> o1_fn_shape ctx fn
Proof
  rw[o1_fn_shape_check_def, o1_fn_shape_def, fn_shape_check_sound,
     fn_inst_wf_def, fn_invoke_ok_def, fn_label_refs_ok_def, no_dret_def,
     gas_var_def, retpc_var_def] >>
  gvs[EVERY_MEM]
  >- metis_tac[MEM_fn_insts_blocks, fn_insts_def]
  >- (first_x_assum drule >> simp[] >> every_case_tac >> simp[])
  >- (first_x_assum drule >> simp[] >> strip_tac >>
      first_x_assum drule >> simp[])
  >> first_x_assum drule >> simp[] >> strip_tac >> res_tac >>
  metis_tac[copy_phi_closed_sound]
QED

Definition o1_ctx_shape_check_def:
  o1_ctx_shape_check ctx <=>
    ALL_DISTINCT (ctx_fn_names ctx) /\
    (case ctx.ctx_entry of
       SOME entry => MEM entry (ctx_fn_names ctx)
     | NONE => F) /\
    ctx_inst_ids_distinct ctx /\
    EVERY (o1_fn_shape_check ctx) ctx.ctx_functions
End

Theorem o1_ctx_shape_check_sound:
  o1_ctx_shape_check ctx ==> o1_ctx_shape ctx
Proof
  rw[o1_ctx_shape_check_def, o1_ctx_shape_def, ctx_wf_def,
     ctx_distinct_fn_names_def, ctx_has_entry_def, EVERY_MEM] >>
  every_case_tac >> gvs[o1_fn_shape_check_sound]
QED

(* ===== PHI coverage and revert-forwarding pairs ===== *)

Definition phis_cover_preds_check_def:
  phis_cover_preds_check fn <=>
    EVERY (\b. EVERY (\s. EVERY (\bb. bb.bb_label = s ==>
       EVERY (\i. i.inst_opcode = PHI ==>
                  MEM b.bb_label (MAP FST (phi_pairs i.inst_operands)))
         bb.bb_instructions) fn.fn_blocks) (bb_succs b)) fn.fn_blocks
End

Theorem phis_cover_preds_check_sound:
  phis_cover_preds_check fn ==> fn_phis_cover_preds fn
Proof
  simp[phis_cover_preds_check_def, fn_phis_cover_preds_def, fn_cfg_edge_def,
       EVERY_MEM] >>
  rpt strip_tac >> rename1 `MEM bb.bb_label (bb_succs b)` >>
  `MEM b.bb_label (MAP FST (phi_pairs inst.inst_operands))` by metis_tac[] >>
  fs[MEM_MAP] >> rename1 `MEM y (phi_pairs _)` >>
  Cases_on `y` >> gvs[] >> metis_tac[]
QED

Theorem phis_cover_preds_check_complete:
  fn_phis_cover_preds fn ==> phis_cover_preds_check fn
Proof
  simp[phis_cover_preds_check_def, fn_phis_cover_preds_def, fn_cfg_edge_def,
       EVERY_MEM] >>
  rpt strip_tac >> gvs[] >>
  rename1 `MEM bb.bb_label (bb_succs b)` >>
  `?v. MEM (b.bb_label, v) (phi_pairs i.inst_operands)` by metis_tac[] >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Definition rfp_check_def:
  rfp_check bb i j <=>
    case (get_instruction bb i, get_instruction bb j) of
      (SOME inst1, SOME inst2) =>
        inst1.inst_opcode = RETURNDATACOPY /\ inst2.inst_opcode = REVERT /\
        i < j /\
        EVERY (\k. case get_instruction bb k of
                     SOME inst => inst.inst_opcode = ASSIGN
                   | NONE => T)
          (GENLIST (\n. SUC i + n) (j - SUC i)) /\
        (case (inst1.inst_operands, inst2.inst_operands) of
           ([p; src; rds], [p'; rds']) =>
             same_after_assigns (REVERSE (TAKE i bb.bb_instructions)) src
               (Lit 0w) /\
             same_after_assigns (REVERSE (TAKE i bb.bb_instructions)) p
               (resolve_block_assigns
                  (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)))
                  p') /\
             same_after_assigns (REVERSE (TAKE i bb.bb_instructions)) rds
               (resolve_block_assigns
                  (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)))
                  rds')
         | _ => F)
    | _ => F
End

Theorem every_genlist_range[local]:
  EVERY P (GENLIST (\n. SUC i + n) (j - SUC i)) <=>
  !k. i < k /\ k < j ==> P k
Proof
  simp[EVERY_GENLIST] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `k - SUC i` mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem rfp_check_eq:
  rfp_check bb i j <=> revert_forward_pair bb i j
Proof
  simp[rfp_check_def, revert_forward_pair_def, every_genlist_range] >>
  Cases_on `get_instruction bb i` >> Cases_on `get_instruction bb j` >>
  simp[] >> every_case_tac >> gvs[] >> eq_tac >> rw[] >> gvs[]
  >~ [`inst.inst_opcode = ASSIGN`]
  >- (first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  Cases_on `get_instruction bb k` >> gvs[] >> res_tac
QED

(* Each RETURNDATACOPY/REVERT pair keeps its witness when the block is cut
   just before the RETURNDATACOPY. *)
Definition rfp_self_contained_check_def:
  rfp_self_contained_check fn <=>
    EVERY (\bb.
      EVERY (\i. EVERY (\j.
          rfp_check bb i j ==>
          rfp_check (bb with bb_instructions := DROP i bb.bb_instructions)
            0 (j - i))
        (FILTER (\k. (EL k bb.bb_instructions).inst_opcode = REVERT)
           (COUNT_LIST (LENGTH bb.bb_instructions))))
      (FILTER (\k. (EL k bb.bb_instructions).inst_opcode = RETURNDATACOPY)
         (COUNT_LIST (LENGTH bb.bb_instructions))))
    fn.fn_blocks
End

Theorem revert_forward_pair_bounds[local]:
  revert_forward_pair bb i j ==>
  i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode = RETURNDATACOPY /\
  (EL j bb.bb_instructions).inst_opcode = REVERT
Proof
  simp[revert_forward_pair_def, get_instruction_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem rfp_self_contained_check_sound:
  rfp_self_contained_check fn /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j ==>
  revert_forward_pair
    (bb with bb_instructions := DROP i bb.bb_instructions) 0 (j - i)
Proof
  rw[rfp_self_contained_check_def, EVERY_MEM] >>
  first_x_assum drule >> strip_tac >>
  drule revert_forward_pair_bounds >> strip_tac >>
  fs[GSYM rfp_check_eq] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[MEM_FILTER, MEM_COUNT_LIST] >>
  disch_then (qspec_then `j` mp_tac) >> simp[MEM_FILTER, MEM_COUNT_LIST]
QED

(* The revert-forward conjunct of inliner_input_guard. *)
Theorem rfp_self_contained_check_guard:
  EVERY rfp_self_contained_check fns ==>
  !fn bb i j. MEM fn fns /\ MEM bb fn.fn_blocks /\ revert_forward_pair bb i j ==>
    revert_forward_pair
      (bb with bb_instructions := DROP i bb.bb_instructions) 0 (j - i)
Proof
  rw[EVERY_MEM] >> metis_tac[rfp_self_contained_check_sound]
QED

(* ===== Inliner shape ===== *)

Definition inliner_fn_shape_check_def:
  inliner_fn_shape_check R rank fn <=>
    canonical_param_prefix fn /\ opaque_use_check fn /\
    retpc_shape_check fn /\ phis_cover_preds_check fn /\
    EVERY (\x. LENGTH (FILTER (\i. MEM x i.inst_outputs) (fn_insts fn)) = 1)
      (FLAT (MAP (\i. i.inst_outputs)
         (FILTER (\i. i.inst_opcode = PARAM) (fn_insts fn)))) /\
    EVERY (\other. other.fn_name <> fn.fn_name ==>
                   ~MEM other.fn_name (fn_labels fn)) R.ctx_functions /\
    EVERY (\inst.
      label_positions_ok inst /\
      (inst.inst_opcode = PHI ==>
         EVERY (\op. case op of Label l => MEM l (fn_labels fn) | _ => T)
           inst.inst_operands) /\
      (inst.inst_opcode = INVOKE ==>
         ALL_DISTINCT inst.inst_outputs /\
         EVERY (\op. case op of Var v => ~MEM v inst.inst_outputs | _ => T)
           (TL inst.inst_operands) /\
         case inst.inst_operands of
           Label l :: args =>
             R.ctx_entry <> SOME l /\ rank l < rank fn.fn_name /\
             EVERY (\callee. callee.fn_name = l ==>
               IS_SOME (fn_retpc_param callee) /\
               LENGTH (rotate_invoke_ops inst.inst_operands) =
                 LENGTH (get_params (fn_entry_insts callee)) /\
               EVERY (\r. raw_return_user_arity r =
                            SOME (LENGTH inst.inst_outputs))
                 (fn_return_insts callee)) R.ctx_functions
         | _ => T))
      (fn_insts fn)
End

Definition inliner_shape_check_def:
  inliner_shape_check rank C <=>
    ctx_inst_ids_distinct C /\ EVERY wf_function C.ctx_functions /\
    ALL_DISTINCT (MAP (\fn. fn.fn_name) C.ctx_functions) /\
    o1_ctx_shape_check (reachable_ctx C) /\
    EVERY (inliner_fn_shape_check (reachable_ctx C) rank)
      (reachable_ctx C).ctx_functions
End

Theorem inliner_inst_check_sound[local]:
  inliner_fn_shape_check R rank fn /\ MEM inst (fn_insts fn) ==>
  label_positions_ok inst /\
  (inst.inst_opcode = PHI ==>
     EVERY (\op. !l. op = Label l ==> MEM l (fn_labels fn))
       inst.inst_operands) /\
  (inst.inst_opcode = INVOKE ==>
     ALL_DISTINCT inst.inst_outputs /\
     EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
       (TL inst.inst_operands))
Proof
  rw[inliner_fn_shape_check_def, EVERY_MEM] >>
  first_x_assum drule >> rw[] >> res_tac >> gvs[]
QED

Theorem inliner_invoke_check_sound[local]:
  inliner_fn_shape_check R rank caller /\ MEM inst (fn_insts caller) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label l :: args ==>
  R.ctx_entry <> SOME l /\ rank l < rank caller.fn_name
Proof
  rewrite_tac[inliner_fn_shape_check_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!i. MEM i (fn_insts caller) ==> _`
    (qspec_then `inst` mp_tac) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem inliner_arity_check_sound[local]:
  inliner_fn_shape_check R rank caller /\ MEM inst (fn_insts caller) /\
  MEM callee R.ctx_functions /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee.fn_name :: args ==>
  IS_SOME (fn_retpc_param callee) /\
  LENGTH (rotate_invoke_ops inst.inst_operands) =
    LENGTH (get_params (fn_entry_insts callee)) /\
  EVERY (\r. raw_return_user_arity r = SOME (LENGTH inst.inst_outputs))
    (fn_return_insts callee)
Proof
  rewrite_tac[inliner_fn_shape_check_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!i. MEM i (fn_insts caller) ==> _`
    (qspec_then `inst` mp_tac) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  first_x_assum (qspec_then `callee` mp_tac) >> simp[]
QED

Theorem inliner_shape_check_sound:
  inliner_shape_check rank C /\
  EVERY fn_defs_reach_uses (reachable_ctx C).ctx_functions ==>
  inliner_shape_ok C
Proof
  rewrite_tac[inliner_shape_check_def, inliner_shape_ok_def, LET_THM] >>
  BETA_TAC >> strip_tac >>
  qabbrev_tac `R = reachable_ctx C` >>
  `!fn. MEM fn R.ctx_functions ==> inliner_fn_shape_check R rank fn` by
    fs[EVERY_MEM] >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[o1_ctx_shape_check_sound]
  >- simp[]
  >- (simp[EVERY_MEM] >> qx_gen_tac `f` >> strip_tac >>
      `inliner_fn_shape_check R rank f` by res_tac >>
      fs[inliner_fn_shape_check_def, phis_cover_preds_check_sound])
  >- (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
      `inliner_fn_shape_check R rank fn` by res_tac >>
      drule inliner_inst_check_sound >> simp[EVERY_MEM] >> strip_tac >>
      fs[inliner_fn_shape_check_def, opaque_use_check_sound,
         retpc_shape_check_sound] >>
      conj_tac >- fs[EVERY_MEM] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      `inliner_fn_shape_check R rank caller` by res_tac >>
      drule_all inliner_arity_check_sound >> simp[])
  >- (rpt gen_tac >> strip_tac >> res_tac >>
      fs[inliner_fn_shape_check_def, EVERY_MEM])
  >- (rpt gen_tac >> strip_tac >> CCONTR_TAC >> fs[] >>
      `inliner_fn_shape_check R rank fn` by res_tac >>
      drule_all inliner_invoke_check_sound >> gvs[])
  >> qexists_tac `rank` >> rw[fn_directly_calls_def] >>
  imp_res_tac lookup_function_MEM >>
  imp_res_tac vyperCompilerTheory.lookup_function_result_name >> gvs[] >>
  `inliner_fn_shape_check R rank func` by res_tac >>
  drule_all inliner_invoke_check_sound >> gvs[]
QED
