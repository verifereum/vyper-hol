Theory typedCopyLoopCounted
Ancestors
  typedCopyCounted placeMemoryFieldsForward externalReturnNormalizeMem
  bodyDeclMemoryCounted bodyDeclMemoryCore fragGasPathMem
  venomState exprLoweringProps list arithmetic

Theorem gas_path_mem_finite_iteration:
  !r i n loop_inv ctx fn s.
    (!j u. loop_inv j u ==> ~u.vs_halted) /\
    (!j u. j < n /\ loop_inv j u ==>
      ?v. gas_path_mem ctx fn u 0 (OK v) /\ loop_inv (SUC j) v) /\
    i + r = n /\ loop_inv i s ==>
    ?t. gas_path_mem ctx fn s 0 (OK t) /\ loop_inv n t
Proof
  Induct >- (rpt strip_tac >> gvs[] >> qexists `s` >>
    `~s.vs_halted` by metis_tac[] >> simp[gas_path_mem_rules]) >>
  rpt strip_tac >>
  `i < n` by decide_tac >>
  `?v. gas_path_mem ctx fn s 0 (OK v) /\ loop_inv (SUC i) v` by metis_tac[] >>
  `?t. gas_path_mem ctx fn v 0 (OK t) /\ loop_inv n t` by
    (first_x_assum irule >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexists `SUC i` >> simp[] >> decide_tac) >>
  qexists `t` >> simp[] >>
  `gas_path_mem ctx fn s (0 + 0) (OK t)` by
    (irule gas_path_mem_then >> qexists `v` >> simp[]) >> gvs[]
QED

Theorem compile_byte_offset_path_mem:
  compile_with_byte_offset op off sa = (out,sb) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME w /\ fn_has_code sa sb fn /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\ alloca_history fn t /\
      eval_operand out t = SOME (w + n2w off) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all compile_with_byte_offset_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule normalize_byte_offset_mem_ok >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx fn s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists `sa` >> simp[]) >>
  `alloca_history fn (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl [`s`, `sa`] >> simp[]) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def,
      same_blocks_def]
QED
