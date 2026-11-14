(* Pointer certificates and ghost framing for a successful transient guard. *)
Theory transientLockPtr
Ancestors
  transientLockProps nonreentrantSource sourceUnitExecution fragGasSeqPtr instSeqComposePtr
  bodyPtrIfExpScalarLoad bodyPtrSignedConvertClamp stmtAppendStorageRunPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline contextCodegenRel codegenRel
  exprLoweringProps emitHelperProps venomInst venomState venomExecSemantics
  instIdxIndep fragExec compileEnv loweringStateRelDefs vyperState
  vyperStorageFootprint words finite_map pred_set list rich_list arithmetic

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

(* The TLOAD output is scalar; reuse the shared comparison/assert certificate. *)
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
  simp[transient_lock_code_def] >> simp[Once inst_seq_ptr_def] >>
  irule (SRULE [GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`id` |-> `st.cs_next_id + 1`, `opc` |-> `EQ`,
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

(* An abort keeps the ghost of the last successful scalar instruction. *)
Theorem transient_lock_abort_ptr_ghost:
  ~ctx_has_dalloca ctx /\ key_taint tn.t_trans (n2w nkey) = {} /\
  (tload (n2w nkey) ss = 1w \/ ~iv /\ ss.vs_call_ctx.cc_static) ==>
  ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn
    (transient_lock_code nkey iv st) ss G' tn'
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  mp_tac (Q.INST [`iv` |-> `T`]
    (SPEC_ALL transient_lock_check_ptr_ghost)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)) >>
  qexistsl_tac [`G'`, `tn'`] >>
  `inst_seq_ptr D 0 ctx func PG G tn
     (transient_lock_code nkey T st) ss G' tn'` by
    fs[transient_lock_code_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (transient_lock_code nkey T st)` by
    simp[transient_lock_code_def, mk_inst_def, is_terminator_def] >>
  Cases_on `iv` >- simp[] >>
  `transient_lock_code nkey F st = transient_lock_code nkey T st ++
     [mk_inst (st.cs_next_id + 4) TSTORE [Lit (n2w nkey); Lit 1w] []]` by
    simp[transient_lock_code_def] >>
  asm_rewrite_tac[] >> Cases_on `tload (n2w nkey) ss = 1w`
  >- (mp_tac (Q.INST [`lo` |-> `0`, `fn` |-> `func`]
        (Q.SPECL [`transient_lock_code nkey T st`, `ss`, `Revert_abort`,
          `revert_state (set_returndata [] (transient_lock_checked_state st nkey ss))`,
          `G`, `tn`, `G'`, `tn'`,
          `[mk_inst (st.cs_next_id + 4) TSTORE [Lit (n2w nkey); Lit 1w] []]`]
          inst_seq_ptr_abort_append)) >>
      simp[transient_lock_code_execution]) >>
  `ss.vs_call_ctx.cc_static` by fs[] >>
  mp_tac (Q.INST [`lo` |-> `0`, `fn` |-> `func`]
    (Q.SPECL [`transient_lock_code nkey T st`, `ss`,
      `transient_lock_checked_state st nkey ss`, `G`, `tn`, `G'`, `tn'`,
      `[mk_inst (st.cs_next_id + 4) TSTORE [Lit (n2w nkey); Lit 1w] []]`,
      `G'`, `tn'`] inst_seq_ptr_append_ok)) >>
  impl_tac
  >- (simp[transient_lock_code_execution] >>
      simp[inst_seq_ptr_def, step_TSTORE_lit_static,
       transient_lock_checked_state_def, update_var_def,
        transient_lock_code_def] >>
      simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, op_taint_def, source_memory_write_ranges_def,
        source_memory_read_ranges_def] >>
      simp[GSYM mk_inst_def, step_inst_non_invoke, step_TSTORE_lit_static] >>
      rpt strip_tac >> gvs[]) >>
  simp[]
QED

Theorem literal_tstore_clean_inst_seq_ptr:
  ~ctx_has_dalloca ctx /\ ~ss.vs_call_ctx.cc_static /\
  (!b. ~((key,b) IN tn.t_trans)) ==>
  inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id TSTORE [Lit key; Lit value] []] ss G tn
Proof
  strip_tac >>
  `step_inst_base (mk_inst id TSTORE [Lit key; Lit value] []) ss =
     OK (tstore key value ss)` by simp[step_TSTORE_lit] >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id TSTORE [Lit key; Lit value] []) ss` by
    (irule append_scalar_inst_check >> simp[tstore_def, op_taint_def] >>
     rpt strip_tac >> gvs[]) >>
  `key_update tn.t_trans key {} = tn.t_trans` by
    (simp[key_update_def, EXTENSION] >>
     qx_gen_tac `p` >> PairCases_on `p` >> simp[] >> metis_tac[]) >>
  `step_taint (mk_inst id TSTORE [Lit key; Lit value] []) ss
     (tstore key value ss) tn = tn` by
    (mp_tac (Q.INST [`tr` |-> `T`, `a` |-> `Lit key`,
       `v` |-> `Lit value`, `slot` |-> `key`, `s` |-> `ss`,
       `s'` |-> `tstore key value ss`]
       (SPEC_ALL scalar_storage_store_taint)) >>
     simp[eval_operand_def, op_taint_def, tstore_def]) >>
  simp[inst_seq_ptr_def, scalar_void_prov]
QED

(* Exactly the three fresh scalar temporaries change the successful ghost. *)
Theorem transient_lock_code_ptr_frame:
  ~ctx_has_dalloca ctx /\ tload (n2w nkey) ss <> 1w /\
  (~iv ==> ~ss.vs_call_ctx.cc_static) /\
  (!b. ~((n2w nkey,b) IN tn.t_trans)) ==>
  ?G' tn'.
    inst_seq_ptr D 0 ctx func PG G tn
      (transient_lock_code nkey iv st) ss G' tn' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `key_taint tn.t_trans (n2w nkey) = {}` by
    (simp[key_taint_def, EXTENSION] >> metis_tac[]) >>
  qabbrev_tac `G1 = DRESTRICT (DRESTRICT (DRESTRICT G
    (COMPL {STRING #"%" (toString st.cs_next_var)}))
    (COMPL {STRING #"%" (toString (st.cs_next_var + 1))}))
    (COMPL {STRING #"%" (toString (st.cs_next_var + 2))})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+
    (STRING #"%" (toString st.cs_next_var),{}) |+
    (STRING #"%" (toString (st.cs_next_var + 1)),{}) |+
    (STRING #"%" (toString (st.cs_next_var + 2)),{})` >>
  `inst_seq_ptr D 0 ctx func PG G tn
    (transient_lock_code nkey T st) ss G1 tn1` by
    (mp_tac (Q.INST [`iv` |-> `T`]
      (SPEC_ALL transient_lock_check_ptr_ghost)) >>
     simp[transient_lock_code_def, Abbr `G1`, Abbr `tn1`]) >>
  qexistsl_tac [`G1`, `tn1`] >> conj_tac
  >- (Cases_on `iv` >- simp[] >>
      `transient_lock_code nkey F st = transient_lock_code nkey T st ++
        [mk_inst (st.cs_next_id + 4) TSTORE [Lit (n2w nkey); Lit 1w] []]` by
        simp[transient_lock_code_def] >>
      asm_rewrite_tac[] >> irule inst_seq_ptr_append_ok >>
      conj_tac
      >- simp[transient_lock_code_def, mk_inst_def, is_terminator_def] >>
      qexistsl_tac [`G1`, `transient_lock_checked_state st nkey ss`, `tn1`] >>
      simp[transient_lock_code_execution] >>
      irule literal_tstore_clean_inst_seq_ptr >>
      gvs[Abbr `tn1`, transient_lock_checked_state_def, update_var_def]) >>
  simp[Abbr `tn1`] >> qx_gen_tac `x` >> strip_tac >>
  `x <> STRING #"%" (toString st.cs_next_var) /\
   x <> STRING #"%" (toString (st.cs_next_var + 1)) /\
   x <> STRING #"%" (toString (st.cs_next_var + 2))` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  simp[Abbr `G1`, FLOOKUP_DRESTRICT, op_taint_def,
       FLOOKUP_UPDATE]
QED
