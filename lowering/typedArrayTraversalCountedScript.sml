Theory typedArrayTraversalCounted
Ancestors
  typedArrayControlCounted typedArrayLoopControlMem fragGasPathMem
  placeMemoryArrayControl placeMemoryArrayForward placeMemoryCopyEffect
  valueEncoding valueEncodingProps vyperValue vyperTypeInvariants
  typedCopyLoopCounted bodyDeclMemoryCounted bodyDeclMemoryCore
  fragExecMem instMemFrontier exprLoweringProps context compileEnv emitHelper
  emitHelperProps venomState venomInst list rich_list arithmetic

Theorem typed_memory_array_addresses_mem_ok[local]:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      comp_return (sp,dp)
   od) sa = ((sp,dp),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def, below_frontier_no_ranges]
QED

Theorem typed_memory_array_addresses_path_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\ alloca_history func u /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_array_addresses_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule typed_memory_array_addresses_mem_ok >> goal_assum (drule_at Any)) >>
  `EVERY (\j. j.inst_opcode <> GAS /\ j.inst_opcode <> INVOKE /\
      ~is_terminator j.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists `sa` >> simp[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl [`s`, `sa`] >> simp[]) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def, same_blocks_def]
QED

(* The recursive callback supplies a counted path and its complete endpoint
   invariant.  In particular, P may retain source/destination frames. *)
Theorem typed_memory_array_body_path_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      comp_return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  fn_has_code sa b4 func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = b5.cs_current_insts ++ typed_sa_backedge_insts id counter inc hdr /\
  (!u. alloca_history func u /\
       eval_operand sp u = SOME (sw + n2w (i * ss)) /\
       eval_operand dp u = SOME (dw + n2w (i * ds)) /\
       (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
       (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
       ~u.vs_halted /\ u.vs_current_bb = b4.cs_current_bb /\
       u.vs_inst_idx = LENGTH b4.cs_current_insts ==>
       ?v. gas_path_mem ctx func u 0 (OK v) /\ P v /\
           lookup_var counter v = SOME (n2w i) /\ ~v.vs_halted /\
           v.vs_current_bb = b5.cs_current_bb /\
           v.vs_inst_idx = LENGTH b5.cs_current_insts) /\
  (!v. P v ==> P (jump_to hdr
     (typed_sa_backedge_state counter inc i v with
       vs_inst_idx := LENGTH b5.cs_current_insts + 2))) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ P t /\
      lookup_var counter t = SOME (n2w (SUC i)) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  strip_tac >> drule_all typed_memory_array_addresses_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `!u. _ ==> ?v. _` drule_all >> strip_tac >>
  `gas_path_mem ctx func v 0 (OK (jump_to hdr
     (typed_sa_backedge_state counter inc i v with
       vs_inst_idx := LENGTH b5.cs_current_insts + 2)))` by
    (irule typed_sa_backedge_path >> simp[eval_operand_def] >>
     qexists `id` >> simp[]) >>
  `gas_path_mem ctx func s (0 + 0) (OK v)` by
    (irule gas_path_mem_then >> qexists `u` >> simp[]) >>
  fs[] >>
  qexists `jump_to hdr (typed_sa_backedge_state counter inc i v with
    vs_inst_idx := LENGTH b5.cs_current_insts + 2)` >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  simp[jump_to_def, typed_sa_backedge_state_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem typed_memory_array_round_frame[local]:
  val_wf stv v /\ (!j. j < N ==> val_wf dtv (elem j)) /\
  (src + type_memory_size stv <= dst \/ dst + N * type_memory_size dtv <= src) /\
  i < N /\ val_in_memory stv v src a.vs_memory /\
  (!j. j < i ==> val_in_memory dtv (elem j)
     (dst + j * type_memory_size dtv) a.vs_memory) /\
  typed_copy_effect ctx func sa head s a dst (N * type_memory_size dtv) /\
  val_in_memory dtv (elem i) (dst + i * type_memory_size dtv) b.vs_memory /\
  typed_copy_effect ctx func sa head a b
    (dst + i * type_memory_size dtv) (type_memory_size dtv) ==>
  val_in_memory stv v src b.vs_memory /\
  (!j. j < SUC i ==> val_in_memory dtv (elem j)
     (dst + j * type_memory_size dtv) b.vs_memory) /\
  typed_copy_effect ctx func sa head s b dst (N * type_memory_size dtv)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_in_memory stv v src b.vs_memory /\
   (!j. j < SUC i ==> val_in_memory dtv (elem j)
      (dst + j * type_memory_size dtv) b.vs_memory)` by
    (irule typed_memory_array_prefix_step >>
     conj_tac >- (qexists `N` >> simp[]) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `i * type_memory_size dtv + type_memory_size dtv <= N * type_memory_size dtv` by
    (`SUC i * type_memory_size dtv <= N * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * _ <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `typed_copy_effect ctx func sa head a b dst (N * type_memory_size dtv)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> decide_tac) >>
  simp[] >> irule typed_copy_effect_then >>
  qexistsl [`sa`, `head`, `a`] >> simp[]
QED

Theorem typed_memory_array_iteration_path_mem:
  val_wf stv v /\
  (!j. j < N ==> val_wf dtv (elem j)) /\
  (src + type_memory_size stv <= dst \/
   dst + N * type_memory_size dtv <= src) /\
  val_in_memory stv v src u.vs_memory /\
  typed_copy_effect ctx func sa head s u dst (N * type_memory_size dtv) /\
  lookup_var counter u = SOME (n2w 0) /\ alloca_history func u /\
  (!i a. i < N /\
     val_in_memory stv v src a.vs_memory /\
     (!j. j < i ==> val_in_memory dtv (elem j)
       (dst + j * type_memory_size dtv) a.vs_memory) /\
     typed_copy_effect ctx func sa head s a dst (N * type_memory_size dtv) /\
     lookup_var counter a = SOME (n2w i) /\ alloca_history func a ==>
     ?b. val_in_memory dtv (elem i)
           (dst + i * type_memory_size dtv) b.vs_memory /\
         typed_copy_effect ctx func sa head a b
           (dst + i * type_memory_size dtv) (type_memory_size dtv) /\
         lookup_var counter b = SOME (n2w (SUC i)) /\
         gas_path_mem ctx func a 0 (OK b) /\ alloca_history func b) ==>
  ?t. val_in_memory stv v src t.vs_memory /\
      (!j. j < N ==> val_in_memory dtv (elem j)
        (dst + j * type_memory_size dtv) t.vs_memory) /\
      typed_copy_effect ctx func sa head s t dst (N * type_memory_size dtv) /\
      lookup_var counter t = SOME (n2w N) /\
      gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `loop_inv = \j a.
    val_in_memory stv v src a.vs_memory /\
    (!k. k < j ==> val_in_memory dtv (elem k)
      (dst + k * type_memory_size dtv) a.vs_memory) /\
    typed_copy_effect ctx func sa head s a dst (N * type_memory_size dtv) /\
    lookup_var counter a = SOME (n2w j) /\ alloca_history func a` >>
  `?t. gas_path_mem ctx func u 0 (OK t) /\ loop_inv N t` suffices_by
    (simp[Abbr `loop_inv`] >> metis_tac[]) >>
  irule (Q.SPECL [`N`, `0`] gas_path_mem_finite_iteration) >>
  simp[Abbr `loop_inv`] >> conj_tac
  >- (rpt strip_tac >> drule typed_copy_effect_endpoint >> simp[]) >>
  rpt strip_tac >> qpat_x_assum `!i a. _` drule_all >> strip_tac >>
  qexists `b` >> simp[] >>
  irule typed_memory_array_round_frame >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
