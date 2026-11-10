(* Runtime-length storage copy: control phases and iteration. *)
Theory assignPlaceDynStorageRuntime
Ancestors
  assignPlaceDynStorageElement placeMemoryCodeLayout storageCopyGasPath
  placeTypedCopyPrimitiveMem fragGasPathMem fragGasMode
  assignPlaceDynStorageLayout fragExec emitHelper emitHelperProps
  exprLoweringProps compileEnv stmtSimStoreCopy
  venomState venomExecSemantics words arithmetic list rich_list

Theorem dyn_storage_header_compile_path_mem[local]:
  emit_op LT [Var cv;len] sa = (lt,s1) /\
  emit_op ISZERO [lt] s1 = (done,s2) /\
  emit_inst JNZ [done;Label exit;Label loop_body] [] s2 = ((),s3) /\
  new_block loop_body s3 = (old,sb) /\ fn_has_code sa sb func /\
  sa.cs_current_insts = [] /\ not_fresh_at sa cv /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand (Var cv) s = SOME (n2w j) /\
  eval_operand len s = SOME (n2w L) /\ j <= L /\ L < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = 0 ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = (if j = L then exit else loop_body) /\
    t.vs_inst_idx = 0
Proof
  strip_tac >>
  drule_all dyn_storage_header_layout >> strip_tac >>
  `cs_extends sa s3 /\ cs_extends s3 sb` by
    (imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
     imp_res_tac cs_extends_new_block >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s3 sb func` by
    (irule fn_has_code_mid >> conj_tac >- simp[] >>
     qexistsl_tac [`sb`, `sa`] >> simp[cs_extends_refl]) >>
  drule_all fn_has_code_new_block >> strip_tac >>
  `s3.cs_current_bb = sa.cs_current_bb /\
   s3.cs_current_insts =
     [mk_inst sa.cs_next_id LT [Var cv;len] [tv];
      mk_inst (sa.cs_next_id+1) ISZERO [Var tv] [dv];
      mk_inst s2.cs_next_id JNZ [Var dv;Label exit;Label loop_body] []]` by
    (gvs[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
         comp_return_def, same_blocks_def, emitted_insts_def]) >>
  `gas_path_mem ctx func s 0
     (OK (jump_to (if j < L then loop_body else exit)
       ((update_var dv (bool_to_word (~(j < L)))
          (update_var tv (bool_to_word (j < L)) s)) with vs_inst_idx := 2)))` by
    (irule typed_memory_array_condition_path_mem >> simp[] >>
     gvs[] >> metis_tac[]) >>
  drule gas_marked_path_from_mem >>
  disch_then (qspec_then `T` assume_tac) >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  simp[store_copy_normalize_def, jump_to_def, update_var_def,
       lookup_var_def] >>
  conj_tac >- simp[venom_state_component_equality] >>
  conj_tac >- (rpt strip_tac >>
    `x <> tv /\ x <> dv` by metis_tac[] >>
    simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  Cases_on `j = L` >> simp[]
QED

Theorem dyn_storage_backedge_frame_mem[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ADD [Var cv;Lit 1w] [nv];
     mk_inst id2 ASSIGN [Var nv] [cv];
     mk_inst id3 JMP [Label hdr] []] /\
  lookup_var cv s = SOME (n2w j) /\ SUC j < dimword (:256) /\
  (!x. not_fresh_at sa x ==> x <> nv /\ x <> cv) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t = s /\
    lookup_var cv t = SOME (n2w (SUC j)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  strip_tac >> drule_all typed_memory_array_backedge_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule gas_marked_path_from_mem >>
  disch_then (qspec_then `T` assume_tac) >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  simp[store_copy_normalize_def, jump_to_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  rpt strip_tac >> `x <> nv /\ x <> cv` by metis_tac[] >> simp[]
QED
