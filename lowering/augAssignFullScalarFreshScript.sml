(* Fresh scalar fragments preserve the surrounding concrete and ghost frame. *)
Theory augAssignFullScalarFresh
Ancestors
  augAssignFullScalar augAssignPtrScalarRun augAssignPtrScalarCertificate
  fragGasFresh fragGasSeqPtr fragGasOriginPtr freshWrites varsExt
  bodyPtrDefs ptrDiscipline exprLoweringProps compileEnv
  venomExecSemantics venomState list rich_list pred_set

Theorem straight_fresh_scalar_origin_ptr_success:
  straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  scalar_code A (emitted_insts sa sb) /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                               (emitted_insts sa sb)))) op ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\ vars_ext t0 t /\
    t = s with vs_vars := t.vs_vars /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s) /\
    (!D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
      gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts), G', tn')) /\
    (!v. not_fresh_at sa v ==>
      FLOOKUP G' v = FLOOKUP G v /\
      op_taint tn' (Var v) = op_taint tn (Var v)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    op_prov G' op = NONE /\ op_taint tn' op = {}
Proof
  strip_tac >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[straight_fresh_def] >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK t` >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  qspecl_then [`emitted_insts sa sb`, `A`, `s`, `t`, `G`, `tn`,
              `ctx`, `func`, `PG`, `explicit`, `bb`] mp_tac
    scalar_code_origin_ptr_success >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `!v. not_fresh_at sa v ==>
       ~MEM v (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (fs[writes_fresh_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `op_prov G' op = NONE /\ op_taint tn' op = {}` by
    (irule scalar_available_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts`
    by simp[] >>
  qexistsl_tac [`G'`, `tn'`] >> simp[lookup_var_def] >> metis_tac[]
QED
