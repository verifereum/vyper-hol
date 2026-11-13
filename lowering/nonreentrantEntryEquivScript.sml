(* TOP-LEVEL: guarded-function lock/release simulation at the actual
   deployment layout. Only the context's slot projection is required, so the
   result also applies inside internal-call frames and deployment contexts. *)
Theory nonreentrantEntryEquiv
Ancestors
  loweringStateRelDefs e2eDefs nonreentrantEquiv transientLockFrameProps
  vyperTypeContract vyperInterpreter vyperState
  compileEnv context venomState exprLoweringProps vyperStorageFootprint
  bodyPtrDefs nonreentrantSource sourceUnitExecution pred_set words
  fragGasSeqPtr transientLockProps ptrSafeRun ptrDiscipline contextCodegenRel
  codegenRel emitHelperProps venomInst venomExecSemantics finite_map
  bodyPtrIfExpScalarLoad bodyPtrSignedConvertClamp instSeqComposePtr

(* Horizon lock words cannot carry relocation taint. *)
Theorem nonreentrant_slot_untainted:
  stor_taint_ok H cx tn ss /\
  MEM nkey (SND H) /\ nkey < dimword (:256) ==>
  !b. ~((n2w nkey, b) IN tn.t_trans)
Proof
  strip_tac >>
  `!b. ~storage_dead H T
    (ss.vs_transient ss.vs_call_ctx.cc_address)
    (w2n ((n2w nkey):bytes32)) b` by
    (gen_tac >> irule nonreentrant_storage_live >> simp[]) >>
  fs[stor_taint_ok_def, cx_dead_def] >>
  Cases_on `ss.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[SUBSET_DEF] >> qx_gen_tac `b` >> strip_tac >>
  qpat_x_assum `!x. x IN tn.t_trans ==> _`
    (qspec_then `(n2w nkey,b)` mp_tac) >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

(* Writing a separated lock leaves the horizon's dead-byte mask intact. *)
Theorem nonreentrant_stor_taint_frame:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  stor_taint_ok H cx tn ss ==>
  stor_taint_ok H cx tn (tstore (n2w nkey) value ss)
Proof
  strip_tac >>
  `!st j b. storage_dead H T (update_storage (n2w nkey) value st) j b =
             storage_dead H T st j b` by
    (rpt gen_tac >> irule nonreentrant_storage_dead_frame >> simp[]) >>
  gvs[stor_taint_ok_def, cx_dead_def, tstore_def,
      combinTheory.APPLY_UPDATE_THM]
QED

(* A literal guard store needs no pointer or tainted operand, including in
   a static frame where execution aborts before writing. *)
Theorem literal_tstore_ptr_inst_ok:
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx func G tn
    (mk_inst id TSTORE [Lit key; Lit value] []) ss
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def, allocas_from_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  Cases_on `ss.vs_call_ctx.cc_static` >>
  simp[mk_inst_def, step_inst_base_opcode_eqs, exec_write2_def,
       eval_operand_def, eval_operands_def, tstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem literal_tstore_inst_seq_ptr:
  ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id TSTORE [Lit key; Lit value] []] ss G' tn'
Proof
  strip_tac >> simp[inst_seq_ptr_def, literal_tstore_ptr_inst_ok] >>
  Cases_on `step_inst_base (mk_inst id TSTORE [Lit key; Lit value] []) ss` >>
  simp[inst_seq_ptr_def]
QED

Theorem transient_lock_check_ptr_ghost:
  ~ctx_has_dalloca ctx /\ key_taint tn.t_trans (n2w nkey) = {} ==>
  ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn
    (TAKE 4 (transient_lock_code nkey iv st)) ss G' tn' /\
    G' = DRESTRICT (DRESTRICT (DRESTRICT G
        (COMPL {STRING #"%" (toString st.cs_next_var)}))
        (COMPL {STRING #"%" (toString (st.cs_next_var + 1))}))
        (COMPL {STRING #"%" (toString (st.cs_next_var + 2))}) /\
    tn' = (tn with t_var := tn.t_var |+
        (STRING #"%" (toString st.cs_next_var),{}) |+
        (STRING #"%" (toString (st.cs_next_var + 1)),{}) |+
        (STRING #"%" (toString (st.cs_next_var + 2)),{}))
Proof
  strip_tac >>
  qexistsl_tac
    [`DRESTRICT (DRESTRICT (DRESTRICT G
       (COMPL {STRING #"%" (toString st.cs_next_var)}))
       (COMPL {STRING #"%" (toString (st.cs_next_var + 1))}))
       (COMPL {STRING #"%" (toString (st.cs_next_var + 2))})`,
     `tn with t_var := tn.t_var |+
       (STRING #"%" (toString st.cs_next_var),{}) |+
       (STRING #"%" (toString (st.cs_next_var + 1)),{}) |+
       (STRING #"%" (toString (st.cs_next_var + 2)),{})`] >>
  simp[] >>
  qabbrev_tac `x0 = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `i0 = mk_inst st.cs_next_id TLOAD [Lit (n2w nkey)] [x0]` >>
  qabbrev_tac `s1 = update_var x0 (tload (n2w nkey) ss) ss` >>
  `step_inst_base i0 ss = OK s1` by
    (simp[Abbr `i0`, Abbr `s1`] >>
     irule transientLockPropsTheory.step_TLOAD >> simp[eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx func G tn i0 ss` by
    (simp[Abbr `i0`] >> irule ifexp_scalar_load_check >>
     simp[op_taint_def] >> qexists_tac `tload (n2w nkey) ss` >>
     simp[Abbr `s1`]) >>
  `step_taint i0 ss s1 tn = tn with t_var := tn.t_var |+ (x0,{})` by
    (simp[Abbr `i0`, Abbr `s1`] >>
     irule ifexp_scalar_load_taint >> simp[eval_operand_def]) >>
  `step_prov PG G i0 s1 = DRESTRICT G (COMPL {x0})` by
    simp[Abbr `i0`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  fs[Abbr `i0`, Abbr `x0`] >>
  simp[transient_lock_code_def] >>
  simp[Once inst_seq_ptr_def] >>
  irule (SRULE [GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`id` |-> `st.cs_next_id + 1`,
             `opc` |-> `EQ`,
             `x` |-> `Var (STRING #"%" (toString st.cs_next_var))`,
             `y` |-> `Lit 1w`,
             `a` |-> `STRING #"%" (toString (st.cs_next_var + 1))`,
             `b` |-> `STRING #"%" (toString (st.cs_next_var + 2))`,
             `G` |-> `DRESTRICT G (COMPL {STRING #"%" (toString st.cs_next_var)})`,
             `tn` |-> `tn with t_var := tn.t_var |+
               (STRING #"%" (toString st.cs_next_var),{})`]
      (SPEC_ALL scalar_iszero_assert_certificate))) >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  simp[run_inst_seq_def, Abbr `s1`, mk_inst_def,
       step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem transient_lock_check_ptr:
  ~ctx_has_dalloca ctx /\ key_taint tn.t_trans (n2w nkey) = {} ==>
  ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn
    (TAKE 4 (transient_lock_code nkey iv st)) ss G' tn'
Proof
  strip_tac >> mp_tac (SPEC_ALL transient_lock_check_ptr_ghost) >>
  simp[] >> metis_tac[]
QED

(* The pointer check follows the executed prefix, so neither a held lock
   nor the static-frame abort asks for an unexecuted suffix. *)
Theorem transient_lock_code_ptr:
  ~ctx_has_dalloca ctx /\ key_taint tn.t_trans (n2w nkey) = {} ==>
  ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn
    (transient_lock_code nkey iv st) ss G' tn'
Proof
  strip_tac >>
  `?G1 tn1. inst_seq_ptr D 0 ctx func PG G tn
     (transient_lock_code nkey T st) ss G1 tn1` by
    (mp_tac (SPEC_ALL transient_lock_check_ptr) >>
     simp[transient_lock_code_def]) >>
  Cases_on `iv` >- (qexistsl_tac [`G1`, `tn1`] >> simp[]) >>
  `transient_lock_code nkey F st = transient_lock_code nkey T st ++
     [mk_inst (st.cs_next_id + 4) TSTORE [Lit (n2w nkey); Lit 1w] []]` by
    simp[transient_lock_code_def] >>
  asm_rewrite_tac[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (transient_lock_code nkey T st)` by
    simp[transient_lock_code_def, mk_inst_def, is_terminator_def] >>
  `run_inst_seq (transient_lock_code nkey T st) ss =
     if tload (n2w nkey) ss = 1w then
       Abort Revert_abort (revert_state (set_returndata []
         (transient_lock_checked_state st nkey ss)))
     else OK (transient_lock_checked_state st nkey ss)` by
    simp[transient_lock_code_execution] >>
  Cases_on `tload (n2w nkey) ss = 1w`
  >- (qexistsl_tac [`G1`, `tn1`] >>
      irule inst_seq_ptr_abort_append >> simp[] >>
      goal_assum (drule_at Any)) >>
  `?G2 tn2. inst_seq_ptr D 0 ctx func PG G1 tn1
     [mk_inst (st.cs_next_id + 4) TSTORE [Lit (n2w nkey); Lit 1w] []]
     (transient_lock_checked_state st nkey ss with
       vs_inst_idx := ss.vs_inst_idx + 4) G2 tn2` by
    (irule literal_tstore_inst_seq_ptr >> simp[]) >>
  qexistsl_tac [`G2`, `tn2`] >>
  irule inst_seq_ptr_append_ok >> simp[] >>
  qexistsl_tac [`G1`, `tn1`] >>
  simp[transient_lock_code_def, arithmeticTheory.ADD_COMM]
QED

Theorem source_typing_function_header:
  source_typing_ok tops am tx /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
  function_header_ok vis mut nr rr name args dflts ret
Proof
  fs[source_typing_ok_def] >>
  metis_tac[check_contract_function_header, listTheory.MEM]
QED


Theorem nonreentrant_entry_lock_source_correct:
  storage_locks_separated (FST H) (SND H) /\
  MEM global_nonreentrant_slot (SND H) /\
  global_nonreentrant_slot < dimword (:256) /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\ fresh_vars_wrt st ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  tload (n2w global_nonreentrant_slot) ss <> 1w ==>
  ?vs' ss'.
    (case cx.nonreentrant_slot of
       NONE => vyperState$raise (vyperState$Error (TypeError "nonreentrant slot missing"))
     | SOME key => acquire_nonreentrant_lock cx.txn.target key
                     (mut = View \/ mut = Pure)) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel H func cenv cx vs' ss'
Proof
  strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[layouts_agree_nonreentrant_slot] >>
  drule function_header_nonreentrant_view >> strip_tac >> simp[] >>
  irule compile_nonreentrant_lock_source_correct >> gvs[]
QED


Theorem nonreentrant_entry_lock_source_revert:
  MEM global_nonreentrant_slot (SND H) /\
  global_nonreentrant_slot < dimword (:256) /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  tload (n2w global_nonreentrant_slot) ss = 1w ==>
  (case cx.nonreentrant_slot of
     NONE => vyperState$raise (vyperState$Error (TypeError "nonreentrant slot missing"))
   | SOME key => acquire_nonreentrant_lock cx.txn.target key
                   (mut = View \/ mut = Pure)) vs =
    (INR (vyperState$Error (RuntimeError "nonreentrant lock")),
     vs with storage_trace := vs.storage_trace ++ [StorageLock global_nonreentrant_slot]) /\
  ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[layouts_agree_nonreentrant_slot] >>
  drule function_header_nonreentrant_view >> strip_tac >> simp[] >>
  irule compile_nonreentrant_lock_source_revert >> gvs[] >> metis_tac[]
QED

(* The source uses this same action on fall-through and ReturnException. *)
Theorem nonreentrant_entry_unlock_source_correct:
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\
  compile_nonreentrant_unlock global_nonreentrant_slot T (mut = View) st = ((),st') ==>
  ?vs' ss'.
    (if ~(mut = View \/ mut = Pure) then
       case cx.nonreentrant_slot of
         NONE => vyperState$return ()
       | SOME key => release_nonreentrant_lock cx.txn.target key
     else vyperState$return ()) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel H func cenv cx vs' ss'
Proof
  strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[layouts_agree_nonreentrant_slot] >>
  drule function_header_nonreentrant_view >> strip_tac >> simp[] >>
  drule_all compile_nonreentrant_unlock_source_correct >>
  Cases_on `mut = View` >> gvs[]
QED

(* The checked entry boundary also keeps already-decoded arguments and local
   buffers, so the simulation can continue into the guarded body. *)

Theorem checked_nonreentrant_entry_lock:
  storage_locks_separated (FST H) (SND H) /\
  MEM global_nonreentrant_slot (SND H) /\
  global_nonreentrant_slot < dimword (:256) /\
  source_typing_ok tops am tx /\ layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\ fresh_vars_wrt st ss /\
  local_ptrs_rel func cenv scopes ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  tload (n2w global_nonreentrant_slot) ss <> 1w ==>
  ?vs' ss'.
    (case cx.nonreentrant_slot of
       NONE => vyperState$raise
         (vyperState$Error (TypeError "nonreentrant slot missing"))
     | SOME key => acquire_nonreentrant_lock cx.txn.target key
                     (mut = View \/ mut = Pure)) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel H func cenv cx vs' ss' /\ fresh_vars_wrt st' ss' /\
    local_ptrs_rel func cenv scopes ss' /\
    !op value. eval_operand op ss = SOME value ==> eval_operand op ss' = SOME value
Proof
  strip_tac >>
  `function_header_ok vis mut T rr name args dflts ret` by
    metis_tac[source_typing_function_header] >>
  `~ss.vs_call_ctx.cc_static` by fs[state_rel_def] >>
  drule_all nonreentrant_entry_lock_source_correct >> strip_tac >>
  drule_all compile_nonreentrant_lock_transient_frame >> strip_tac >>
  gvs[] >> metis_tac[]
QED
