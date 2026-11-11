(* Dynamic typed-copy prefix: representation supplies the checked length. *)
Theory bodyPtrIntCallArrayHeader
Ancestors bodyPtrBopInHeaderControl bodyPtrBopInMemoryContents bodyPtrBopInElementLoad
  bodyPtrIntCallFieldOffset augAssignPtrStore annAssignPtrLength
  typedCopyLayoutPtr valueEncodingProps vyperTyping venomMemDefs bodyPtrDefs
  venomExecSemantics venomState ptrDiscipline fragGasPathPtr
  words finite_map pred_set arithmetic

Theorem intcall_dynamic_checked_length[local]:
  !D ctx fn PG G tn s bb id src hdr flag valid stv dtv scap dcap vs a.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [hdr]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) GT [Var hdr;Lit (n2w dcap)] [flag]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) ISZERO [Var flag] [valid]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ASSERT [Var valid] []) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    value_has_type (ArrayTV dtv (Dynamic dcap)) (ArrayV (DynArrayV vs)) /\
    dcap < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
    ?H tf z.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
      z = (update_var valid 1w (update_var flag 0w
        (update_var hdr (n2w (LENGTH vs)) s)) with vs_inst_idx := s.vs_inst_idx+4) /\
      tf = (tn with t_var := tn.t_var |+ (hdr,{}) |+ (flag,{}) |+ (valid,{})) /\
      (hdr <> flag /\ hdr <> valid ==> FLOOKUP H hdr = NONE) /\
      (!x. x <> hdr /\ x <> flag /\ x <> valid ==> FLOOKUP H x = FLOOKUP G x)
Proof
  rpt gen_tac >> strip_tac >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    metis_tac[dynarray_memory_header_clean] >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mload_def, valueEncodingTheory.mem_word_at_def]) >>
  `LENGTH vs <= dcap` by fs[value_has_type_def] >>
  drule_all membership_positioned_mload_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[] >>
  drule_all membership_loaded_header_capacity_path >>
  strip_tac >> metis_tac[]
QED

Theorem intcall_dynamic_checked_prefix[local]:
  (do len <- compile_ptr_load F NONE LocMemory (Var src);
      flag <- emit_op GT [len;Lit (n2w dcap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sm) /\
  fn_has_code sa sm fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  value_has_type (ArrayTV dtv (Dynamic dcap)) (ArrayV (DynArrayV vs)) /\
  dcap < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tf z.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK z) /\
    z.vs_current_bb = sm.cs_current_bb /\
    z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
    eval_operand len z = SOME (n2w (LENGTH vs)) /\
    op_prov H len = NONE /\ op_taint tf len = {} /\
    (z with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all bodyPtrBopInHeaderCodeTheory.membership_runtime_header_code >> strip_tac >>
  drule (SRULE [] (GEN_ALL bodyPtrBopInHeaderCodeTheory.membership_runtime_header_layout)) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  qpat_x_assum `s.vs_current_bb = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  drule_all intcall_dynamic_checked_length >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       op_taint_def, venom_state_component_equality] >>
  conj_tac
  >- simp[op_prov_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var) /\
   x <> STRING #"%" (toString (sa.cs_next_var+1)) /\
   x <> STRING #"%" (toString (sa.cs_next_var+2))` by
    (fs[compileEnvTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_ADD]) >>
  simp[]
QED
