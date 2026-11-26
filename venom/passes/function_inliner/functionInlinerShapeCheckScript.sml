(* An executable check for the inliner's syntactic shape premise.
 *
 * TOP-LEVEL:
 *   o1_ctx_shape_check, o1_ctx_shape_check_sound
 *   inliner_shape_check, inliner_shape_check_sound
 *
 * The call-rank existential is checked against a rank the caller supplies.
 * Definite assignment stays a premise: its executable check rejects PHIs.
 *)
Theory functionInlinerShapeCheck
Ancestors
  functionInlinerContract o1SourceUnitCheck defsReachCheck o1PassContract
  unitShapeDefs dretDesugarDefs fcgDefs venomWf venomInst list
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

(* ===== Inliner shape ===== *)

Definition inliner_fn_shape_check_def:
  inliner_fn_shape_check R rank fn <=>
    canonical_param_prefix fn /\ opaque_use_check fn /\
    retpc_shape_check fn /\
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

Theorem lookup_function_SOME_name[local]:
  !fns. lookup_function a fns = SOME f ==> MEM f fns /\ f.fn_name = a
Proof
  Induct >> rw[lookup_function_def, FIND_thm] >> gvs[lookup_function_def]
QED

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
  >- (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
      `inliner_fn_shape_check R rank fn` by res_tac >>
      drule inliner_inst_check_sound >> simp[EVERY_MEM] >> strip_tac >>
      fs[inliner_fn_shape_check_def, opaque_use_check_sound,
         retpc_shape_check_sound] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      `inliner_fn_shape_check R rank caller` by res_tac >>
      drule_all inliner_arity_check_sound >> simp[])
  >- (rpt gen_tac >> strip_tac >> res_tac >>
      fs[inliner_fn_shape_check_def, EVERY_MEM])
  >- (rpt gen_tac >> strip_tac >> CCONTR_TAC >> fs[] >>
      `inliner_fn_shape_check R rank fn` by res_tac >>
      drule_all inliner_invoke_check_sound >> gvs[])
  >> qexists_tac `rank` >> rw[fn_directly_calls_def] >>
  drule lookup_function_SOME_name >> strip_tac >>
  `inliner_fn_shape_check R rank func` by res_tac >>
  drule_all inliner_invoke_check_sound >> gvs[]
QED
