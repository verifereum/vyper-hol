Theory bodyPtrIfExpStoragePhases
Ancestors
  bodyPtrIfExpStorageLoop bodyPtrIfExpMaterializeWord bodyPtrIfExpScalarLoad
  slotCopyExecution stmtAppendStorageRunPtr fragGasSeqPtr exprLoweringProps
  venomExecSemantics venomState venomInst ptrDiscipline finite_map

(* Semantic inputs, rather than supplied per-instruction outcomes, form the
   public phase interface. The runtime cursor is advanced only by the path. *)
Theorem ifexp_copy_read_phase:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\
  eval_operand src s = SOME p /\ eval_operand counter s = SOME q /\
  op_taint tn src = {} /\ op_taint tn counter = {} ==>
  ?t G' tn'.
    run_inst_seq [mk_inst aid ADD [src;counter] [key];
      mk_inst lid load [Var key] [loaded]] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst aid ADD [src;counter] [key];
       mk_inst lid load [Var key] [loaded]] s G' tn' /\
    t = update_var loaded (slot_copy_word load s (p+q))
          (update_var key (p+q) s) /\
    op_prov G' (Var loaded) = NONE /\
    op_taint tn' (Var loaded) =
      (if load = SLOAD then key_taint tn.t_stor (p+q)
       else key_taint tn.t_trans (p+q)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> key /\ x <> loaded ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `r = update_var key (p+q) s` >>
  qabbrev_tac `s1 = r with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = slot_copy_word load s (p+q)` >>
  `step_inst_base (mk_inst aid ADD [src;counter] [key]) s = OK r` by
    simp[Abbr `r`, step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  `step_inst_base (mk_inst lid load [Var key] [loaded]) s1 =
     OK (update_var loaded v s1)` by
    (gvs[] >> simp[Abbr `s1`, Abbr `r`, Abbr `v`, step_inst_base_def,
      mk_inst_def, exec_read1_def, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE, slot_copy_word_def, sload_def,
      tload_def, contract_storage_def, contract_transient_def]) >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst aid ADD [src;counter] [key]) r` >>
  qabbrev_tac `tn1 = step_taint (mk_inst aid ADD [src;counter] [key]) s r tn` >>
  qexistsl_tac [`update_var loaded v r`,
    `step_prov PG G1 (mk_inst lid load [Var key] [loaded]) (update_var loaded v s1)`,
    `step_taint (mk_inst lid load [Var key] [loaded]) s1 (update_var loaded v s1) tn1`] >>
  reverse conj_tac
  >- (conj_tac
      >- (irule ifexp_copy_read_checks >> simp[Abbr `G1`, Abbr `tn1`] >>
          qexists_tac `p+q` >> simp[Abbr `r`, Abbr `s1`]) >>
      simp[Abbr `r`, Abbr `v`] >>
      `tn1 = tn with t_var := tn.t_var |+ (key,{})` by
        (simp[Abbr `tn1`] >> irule scalar_add_taint >> simp[update_var_def]) >>
      `eval_operand (Var key) s1 = SOME (p+q)` by
        simp[Abbr `s1`, eval_operand_def, lookup_var_def,
             update_var_def, FLOOKUP_UPDATE] >>
      `step_taint (mk_inst lid load [Var key] [loaded]) s1
         (update_var loaded (slot_copy_word load s (p+q)) s1) tn1 =
         tn1 with t_var := tn1.t_var |+ (loaded,
           if load = SLOAD then key_taint tn1.t_stor (p+q)
           else if load = TLOAD then key_taint tn1.t_trans (p+q) else {})` by
        (irule ifexp_materialize_load_taint >> simp[] >> fs[]) >>
      simp[op_prov_def, step_prov_def, out_prov_def,
        set_prov_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE,
        FLOOKUP_DRESTRICT, lookup_var_def, update_var_def] >>
      rpt strip_tac >> simp[Abbr `G1`, scalar_step_old_prov] >>
      gvs[FLOOKUP_DRESTRICT, scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]) >>
  gvs[] >> simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
    exec_read1_def, Abbr `r`, Abbr `v`, slot_copy_word_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    sload_def, tload_def, contract_storage_def, contract_transient_def]
QED
