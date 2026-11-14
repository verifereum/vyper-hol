(* Counted normalized-buffer copies for both immutable base forms. *)
Theory immutableNormalizedCopyPathMem
Ancestors
  immutableFixedOptionPathMem immutableConstructorRelation immutableDeployAssignBytes
  valueEncodingProps loweringSlice exprLoweringProps context compileEnv fragExec fragGasMode localPtrsProps
  venomState venomExecSemantics loweringStateRelDefs words arithmetic list finite_map

Theorem immutable_normalized_copy_path_terminal[local]:
  t = r with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
    vs_immutables := t.vs_immutables|> /\
  t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
  mem_cont_sim ctx func r (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x r) /\
  t.vs_memory = (mcopy off b (32*n) r).vs_memory /\
  mem_bytes_at off (32*n) t.vs_memory = mem_bytes_at b (32*n) r.vs_memory /\
  (!q k. q+k <= off \/ off+32*n <= q ==>
    mem_bytes_at q k t.vs_memory = mem_bytes_at q k r.vs_memory) /\
  gas_marked_path T ctx func r 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  well_formed_type_value dtv /\
  type_memory_size dtv = 32*n /\ immutable_value_admissible dtv v /\
  val_in_memory dtv v b r.vs_memory /\
  alloca_inv r /\ alloca_room ctx func r /\
  ~r.vs_halted /\ r.vs_current_bb = sb.cs_current_bb ==>
  ?z. mem_cont_sim ctx func r z /\
    z.vs_allocas = r.vs_allocas /\ z.vs_alloca_next = r.vs_alloca_next /\
    alloca_inv z /\ alloca_room ctx func z /\
    val_in_memory dtv v off z.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off (type_memory_size dtv) z.vs_memory) /\
    (!q k. q+k <= off \/ off+type_memory_size dtv <= q ==>
      mem_bytes_at q k z.vs_memory = mem_bytes_at q k r.vs_memory) /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x r) /\
    z = r with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory;
      vs_immutables := z.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_marked_path T ctx func r 0 (OK z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_wf dtv v` by metis_tac[immutable_admissible_val_wf] >>
  `val_in_memory dtv v off (mcopy off b (32*n) r).vs_memory` by
    (qpat_assum `val_in_memory dtv v b _` mp_tac >>
     qpat_assum `val_wf dtv v` mp_tac >>
     qpat_assum `type_memory_size dtv = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule mcopy_establishes_val_in_memory >> simp[]) >>
  `immutable_value_bytes_rel dtv v (mem_bytes_at b (32*n) r.vs_memory)` by
    metis_tac[immutable_memory_bytes] >>
  suspend "terminal_frame"
QED

Resume immutable_normalized_copy_path_terminal[terminal_frame]:
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (qpat_assum `t = _` (mp_tac o Q.AP_TERM `\z. (z.vs_halted,z.vs_current_bb)`) >>
     qpat_assum `~r.vs_halted` mp_tac >>
     qpat_assum `r.vs_current_bb = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `alloca_inv t /\ alloca_room ctx func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `alloca_inv r` mp_tac >>
     qpat_assum `alloca_room ctx func r` mp_tac >>
     qpat_assum `t.vs_allocas = _` mp_tac >>
     qpat_assum `t.vs_alloca_next = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 4 strip_tac >>
     conj_tac >- metis_tac[alloca_inv_fields] >>
     irule alloca_room_fields >> qexists_tac `r` >> simp[]) >>
  `t with vs_inst_idx := LENGTH sb.cs_current_insts =
    r with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
      vs_immutables := t.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|>` by
    (qpat_assum `t = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[venom_state_component_equality]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qpat_x_assum `t = _` kall_tac >>
  simp[NoAsms] >> asm_rewrite_tac[lookup_var_def] >>
  pure_rewrite_tac[mcopy_mem_bytes_at_same] >>
  rpt conj_tac
  >- asm_rewrite_tac[]
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac)
  >- (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  simp[NoAsms, venom_state_component_equality] >> asm_rewrite_tac[]
QED

Finalise immutable_normalized_copy_path_terminal[local]

Theorem immutable_normalized_copy_mem_path_endpoint:
  compile_imm_store_words imm buf.buf_operand dst n 0 sn = ((),sb) /\
  fn_has_code sn sb func /\ sn.cs_current_bb = sb.cs_current_bb /\
  eval_operand buf.buf_operand r = SOME (n2w b) /\
  eval_operand dst r = SOME (n2w off) /\
  (!region. imm = SOME region ==> eval_operand region r = SOME 0w) /\
  (!x. buf.buf_operand = Var x ==> not_fresh_at sn x) /\
  (!x. dst = Var x ==> not_fresh_at sn x) /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sn x) /\ 0 < n /\
  well_formed_type_value dtv /\
  type_memory_size dtv = 32*n /\ immutable_value_admissible dtv v /\
  val_in_memory dtv v b r.vs_memory /\
  b+32*n <= r.vs_alloca_next /\ off+32*n <= r.vs_alloca_next /\
  b+32*n < dimword (:256) /\ off+32*n < dimword (:256) /\
  regions_disjoint off (32*n) b (32*n) /\
  alloca_inv r /\ alloca_room ctx func r /\
  ~r.vs_halted /\ r.vs_current_bb = sb.cs_current_bb /\
  r.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?z. mem_cont_sim ctx func r z /\
    z.vs_allocas = r.vs_allocas /\ z.vs_alloca_next = r.vs_alloca_next /\
    alloca_inv z /\ alloca_room ctx func z /\
    val_in_memory dtv v off z.vs_memory /\
    immutable_value_bytes_rel dtv v (mem_bytes_at off (type_memory_size dtv) z.vs_memory) /\
    (!q k. q+k <= off \/ off+type_memory_size dtv <= q ==>
      mem_bytes_at q k z.vs_memory = mem_bytes_at q k r.vs_memory) /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x r) /\
    z = r with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory;
      vs_immutables := z.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_marked_path T ctx func r 0 (OK z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `b+0+32*n <= r.vs_alloca_next /\ off+0+32*n <= r.vs_alloca_next /\
   b+0+32*n < dimword (:256) /\ off+0+32*n < dimword (:256) /\
   (off+0+32*n <= b+0 \/ b+0+32*n <= off+0)` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  mp_tac (Q.INST [`imm` |-> `imm`, `src` |-> `buf.buf_operand`,
    `dst` |-> `dst`, `n` |-> `n`, `off` |-> `0`, `sa` |-> `sn`,
    `sb` |-> `sb`, `a` |-> `b`, `b` |-> `off`, `s` |-> `r`,
    `func` |-> `func`, `ctx` |-> `ctx`]
    immutable_fixed_copy_operand_mem_path_option) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  rule_assum_tac (PURE_REWRITE_RULE [ADD_0]) >>
  drule_all immutable_normalized_copy_path_terminal >>
  disch_then ACCEPT_TAC
QED
