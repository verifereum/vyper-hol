(* A flat memory copy fixes its state and ghosts before the dead mask. *)
Theory bodyFullMemoryCopy
Ancestors
  typedCopyOriginPtrBase typedMemoryCopy robustCopyTransportPtr
  fragGasOriginPtr fragGasSeqPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  context contextCodegenRel codegenRel unitTransformDefs instMemFrontier
  memSafeRun fragExec emitHelper emitHelperProps compileEnv
  venomExecSemantics venomInst venomState valueEncoding valueEncodingDefs
  valueEncodingProps exprSimProps finite_map pred_set list rich_list words

Theorem body_full_memory_copy_path:
  compile_copy_memory (Var xd) (Var xs) n sa = ((),sb) /\
  type_memory_size tv = n /\ val_wf tv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s n /\ ptr_covers G tn xd s n /\
  w2n sw + n < dimword (:256) /\ w2n dw + n < dimword (:256) /\
  (n = 0 \/ w2n sw + n <= s.vs_alloca_next) /\
  (n = 0 \/ w2n dw + n <= s.vs_alloca_next) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) n s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_footprint tv v <= n` by metis_tac[val_footprint_le] >>
  Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n dw) mem` by
        (rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >>
         simp[] >> qexistsl_tac [`w2n sw`,`0`,`mem`] >> simp[mem_bytes_at_def]) >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[typed_copy_state_frame_refl, gas_origin_ptr_path_rules] >>
      first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `0 < n /\ n < dimword (:256)` by decide_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY
    [Var xd;Var xs;Lit (n2w n)] []` >>
  qabbrev_tac `sc = mcopy (w2n dw) (w2n sw) n s` >>
  qabbrev_tac `tf = step_taint inst s sc tn` >>
  `step_inst_base inst s = OK sc` by
    simp[Abbr `inst`,Abbr `sc`,step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def] >>
  `step_prov PG G inst sc = G /\ tf.t_var = tn.t_var /\
   tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
   tf.t_mem = (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw+n}) UNION
     {w2n dw+i | i < n /\ w2n sw+i IN tn.t_mem}` by suspend "ghost" >>
  `!mem. mem_agree_outside tf.t_mem sc.vs_memory mem ==>
    val_in_memory tv v (w2n dw) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- metis_tac[val_footprint_le] >>
     qexistsl_tac [`s.vs_memory`,`sc.vs_memory`,`n`,`w2n sw`,
       `tn.t_mem`,`tf.t_mem`] >>
     simp[Abbr `sc`,valueEncodingPropsTheory.mcopy_mem_bytes_at_same]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
   sb.cs_blocks = sa.cs_blocks` by suspend "code" >>
  `val_in_memory tv v (w2n dw) sc.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `typed_copy_state_frame sa (w2n dw) n s
    (sc with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[Abbr `sc`,typed_copy_mcopy_state_frame] >>
  `!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)` by suspend "exterior" >>
  qexistsl_tac [`sc with vs_inst_idx := LENGTH sb.cs_current_insts`,`G`,`tf`] >>
  conj_tac >- suspend "path" >>
  simp[op_taint_def] >>
  simp[Abbr `sc`,mcopy_def,write_memory_with_expansion_def,lookup_var_def]
QED

Resume body_full_memory_copy_path[exterior]:
  qpat_x_assum `tf.t_mem = _` SUBST1_TAC >>
  rw[EQ_IMP_THM] >> gvs[] >> decide_tac
QED

Resume body_full_memory_copy_path[ghost]:
  simp[Abbr `tf`,Abbr `inst`,Abbr `sc`,step_prov_def,set_prov_def,out_prov_def,
       step_taint_def,mk_inst_def,set_var_taint_def,DRESTRICT_UNIV,
       store_taint_def,adopt_reset_def,mem_taint_def,imm_taint_def,
       step_writes_def,source_memory_write_ranges_def,fixed_source_write_range_def,
       sized_source_write_range_def,written_taint_def,range_bytes_def,
       new_site_bytes_def,mcopy_def,write_memory_with_expansion_def,
       eval_operand_def,FLOOKUP_DEF,pred_setTheory.EXTENSION] >> metis_tac[]
QED

Resume body_full_memory_copy_path[code]:
  qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >> Cases_on `n` >>
  simp[compile_copy_memory_def,emit_void_def,emit_inst_def,comp_bind_def,
       fresh_id_def,emit_def,comp_return_def,Abbr `inst`] >>
  strip_tac >> gvs[]
QED

Resume body_full_memory_copy_path[path]:
  gen_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst` by
    (gvs[fn_has_code_def,rich_listTheory.IS_PREFIX_APPEND,
         get_instruction_def,listTheory.EL_APPEND_EQN]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by suspend "pointer" >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`,inst_mem_below_frontier_def,inst_dload_in_section_def,
         mk_inst_def,source_memory_read_ranges_def,source_memory_write_ranges_def,
         sized_source_write_range_def,eval_operand_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (sc with vs_inst_idx := SUC s.vs_inst_idx),G,tf)` by
    (`inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
      inst.inst_opcode <> GAS` by
       simp[Abbr `inst`,mk_inst_def,is_terminator_def] >>
     drule_all straight_line_origin_ptr_edge >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
     simp[Abbr `inst`,Abbr `tf`,mk_inst_def,is_terminator_def]) >>
  `~sc.vs_halted` by simp[Abbr `sc`,mcopy_def,write_memory_with_expansion_def] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  drule (cj 2 gas_origin_ptr_path_rules) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Resume body_full_memory_copy_path[pointer]:
  gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def,Abbr `inst`,mk_inst_def,step_inst_def,taint_ok_def,
       op_taint_def,Abbr `sc`,mcopy_def,write_memory_with_expansion_def,
       access_ok_def,source_memory_write_ranges_def,source_memory_read_ranges_def,
       sized_source_write_range_def,eval_operand_def] >>
  conj_tac >- simp[memLocDefsTheory.mem_write_ops_def,memLocDefsTheory.mem_read_ops_def] >>
  qpat_x_assum `op_taint tn (Var xs) = {}` mp_tac >>
  qpat_x_assum `op_taint tn (Var xd) = {}` mp_tac >>
  simp[op_taint_def] >> ntac 2 disch_tac >>
  qx_gen_tac `operand` >> Cases_on `operand` >> simp[] >> metis_tac[]
QED

Finalise body_full_memory_copy_path
