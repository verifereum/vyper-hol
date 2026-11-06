(* Installation of the finite load/store branch, separately from allocation. *)
Theory bodyPtrMakeArrayOneSlotInstalled
Ancestors
  bodyPtrMakeArrayOneSlot bodyPtrMakeArrayPrimitiveInstall exprSimStorageCopy
  exprLoweringProps emitHelperProps context fragExec compileEnv emitHelper
  venomState venomInst ptrDiscipline finite_map pred_set list rich_list words

Theorem external_one_slot_shape:
  emit_op opc [src] sa = (Var tmp,sl) /\
  emit_void MSTORE [Var dst; Var tmp] sl = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id opc [src] [tmp];
     mk_inst (sa.cs_next_id + 1) MSTORE [Var dst; Var tmp] []] /\
  (!x. not_fresh_at sa x ==> tmp <> x)
Proof
  strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  simp[APPEND_ASSOC, not_fresh_at_def] >> metis_tac[]
QED

Theorem external_one_slot_fetch:
  emit_op opc [src] sa = (Var tmp,sl) /\
  emit_void MSTORE [Var dst; Var tmp] sl = ((),sb) /\ fn_has_code sa sb fn ==>
  ?bb.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id opc [src] [tmp]) /\
    get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
      SOME (mk_inst (sa.cs_next_id + 1) MSTORE [Var dst; Var tmp] []) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2 /\
    (!x. not_fresh_at sa x ==> tmp <> x)
Proof
  strip_tac >> drule_all external_one_slot_shape >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  first_assum (qspec_then `0` mp_tac) >>
  first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1] >>
  metis_tac[]
QED

Theorem external_one_slot_installed:
  emit_op (if tr then TLOAD else SLOAD) [src] sa = (Var tmp,sl) /\
  emit_void MSTORE [Var dst; Var tmp] sl = ((),sb) /\ fn_has_code sa sb fn /\
  copy_old_operand sa src /\ not_fresh_at sa dst /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ eval_operand src s = SOME key /\
  step_inst_base (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [src] [tmp]) s =
    OK (update_var tmp w s) /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME (n2w b) /\
  b + 32 < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?sf H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    mem_word_at b sf.vs_memory = w /\
    lookup_var dst sf = SOME (n2w b) /\ ptr_covers H tm dst sf 32 /\
    mem_agree_outside {i | b <= i /\ i < b + 32} sf.vs_memory s.vs_memory /\
    tm.t_mem = (tn.t_mem DIFF {i | b <= i /\ i < b + 32}) UNION
      {b + k | k IN key_taint (if tr then tn.t_trans else tn.t_stor) key} /\
    (!i. i < b \/ b + 32 <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ op_prov H (Var x) = op_prov G (Var x) /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    copy_static sf = copy_static s /\ LENGTH s.vs_memory <= LENGTH sf.vs_memory
Proof
  strip_tac >> drule_all external_one_slot_fetch >> strip_tac >>
  `tmp <> dst` by metis_tac[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [src] [tmp]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sa.cs_next_id + 1) MSTORE [Var dst; Var tmp] [])` by metis_tac[] >>
  Cases_on `tr` >> gvs[]
  >- (mp_tac (Q.INST [`opc` |-> `TLOAD`, `id` |-> `sa.cs_next_id`,
          `sid` |-> `sa.cs_next_id + 1`] (SPEC_ALL external_one_slot_endpoint)) >>
      (impl_tac >- (simp[] >> metis_tac[])) >>
      strip_tac >> qexistsl_tac [`sf`, `H`, `tm`] >>
      gvs[op_prov_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`opc` |-> `SLOAD`, `id` |-> `sa.cs_next_id`,
      `sid` |-> `sa.cs_next_id + 1`] (SPEC_ALL external_one_slot_endpoint)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> qexistsl_tac [`sf`, `H`, `tm`] >>
  gvs[op_prov_def] >> metis_tac[]
QED
