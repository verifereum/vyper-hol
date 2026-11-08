Theory typedCopyArrayEntryPathMem
Ancestors
  typedArrayLoopLayoutMem typedCopyControlPathMem exprSimBopRestWordLoopPath
  fragGasMode fragGasPathMem venomState venomExecSemantics venomInst
  exprLoweringProps words arithmetic list rich_list typedNormalizeDynarray
  bodyDeclMemoryCounted exprSimDefs emitHelper context compileEnv valueEncoding

Theorem typed_sa_pointer_path_mem:
  code =
    [mk_inst id MUL [Var ctr; Lit (n2w src_stride)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w dst_stride)] [dso];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var dso] [dp]] /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code bb.bb_instructions /\
  ALL_DISTINCT [so;dso;sp;dp] /\ ~MEM ctr [so;dso;sp;dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so;dso;sp;dp]) /\
  eval_operand src s = SOME (n2w source_base) /\
  eval_operand dst s = SOME (n2w dest_base) /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 ==>
  ?u. gas_path_mem ctx fn s 0 (OK u) /\ u.vs_inst_idx = 4 /\
    eval_operand (Var sp) u = SOME (n2w (source_base + src_stride*i)) /\
    eval_operand (Var dp) u = SOME (n2w (dest_base + dst_stride*i)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. ~MEM x [so;dso;sp;dp] ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_sa_pointer_run >>
  disch_then (qspecl_then [`src_stride`, `id`, `dst_stride`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexists_tac `q with vs_inst_idx := 4` >> conj_tac
  >- (mp_tac (Q.INST [`code` |-> `code`, `t` |-> `q`, `memory` |-> `T`]
               rest_word_sequence_marked) >>
      simp[gas_marked_path_def, mk_inst_def, is_terminator_def] >>
      disch_then irule >> gvs[mk_inst_def]) >>
  fs[venom_state_component_equality, eval_operand_def, lookup_var_def]
QED

Theorem typed_dynarray_prefix_path_mem:
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  mload (w2n p) s = n2w n /\ n <= cap /\ cap < dimword(:256) /\
  32 <= sz /\ 32 <= dz /\
  w2n p+sz <= s.vs_alloca_next /\ w2n d+dz <= s.vs_alloca_next /\
  (w2n p+sz <= w2n d \/ w2n d+dz <= w2n p) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\ ~q.vs_halted /\
    q.vs_current_bb = sa.cs_current_bb /\
    q.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) q = SOME (n2w n) /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+3))) q =
      SOME (n2w (w2n p+32)) /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+4))) q =
      SOME (n2w (w2n d+32)) /\
    q.vs_memory = (mstore (w2n d) (n2w n) s).vs_memory /\
    mem_bytes_at (w2n p) sz q.vs_memory = mem_bytes_at (w2n p) sz s.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+32 <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_dynarray_compiler_prefix >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `sm` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `sm.cs_current_insts = _ ++ code` >>
  `ALL_DISTINCT ["%" ++ toString sa.cs_next_var;
    "%" ++ toString (sa.cs_next_var+1); "%" ++ toString (sa.cs_next_var+2);
    "%" ++ toString (sa.cs_next_var+3); "%" ++ toString (sa.cs_next_var+4)]` by
    simp[ASCIInumbersTheory.toString_inj] >>
  `!x. src = Var x \/ dst = Var x ==>
    ~MEM x ["%" ++ toString sa.cs_next_var;
    "%" ++ toString (sa.cs_next_var+1); "%" ++ toString (sa.cs_next_var+2);
    "%" ++ toString (sa.cs_next_var+3); "%" ++ toString (sa.cs_next_var+4)]` by
    (rpt gen_tac >> disch_tac >>
     `not_fresh_at sa x` by metis_tac[] >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]) >>
  suspend "path"
QED
Resume typed_dynarray_prefix_path_mem[path]:
  qpat_x_assum `Abbrev (code = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all typed_dynarray_prologue_window_run >> strip_tac >>
  `emitted_insts sa sm = code` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `LENGTH code = 7 /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode) code` by
    simp[mk_inst_def, is_terminator_def] >>
  qpat_x_assum `code = _` kall_tac >>
  `gas_path_mem ctx fn s 0 (OK (q with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >>
     simp[IS_PREFIX_APPEND, same_blocks_def]) >>
  suspend "finish"
QED
Resume typed_dynarray_prefix_path_mem[finish]:
  qexists_tac `q with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> rpt strip_tac >>
  `x <> "%" ++ toString sa.cs_next_var /\
   x <> "%" ++ toString (sa.cs_next_var+1) /\
   x <> "%" ++ toString (sa.cs_next_var+2) /\
   x <> "%" ++ toString (sa.cs_next_var+3) /\
   x <> "%" ++ toString (sa.cs_next_var+4)` by
    (gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]) >>
  first_x_assum irule >> gvs[]
QED
Finalise typed_dynarray_prefix_path_mem
