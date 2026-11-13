Theory typedDynarrayForwardCounted
Ancestors
  typedArraySemanticCounted typedArrayTraversalCounted typedArrayControlCounted
  allocaHistory placeMemoryCodeLayout
  placeMemoryDynarrayForward placeMemoryArrayForward placeMemoryTypedBase freshWrites
  placeMemoryCopyEffect placeMemoryCopyFrames valueEncoding exprSimAggregateEncoding
  bodyDeclMemoryCounted bodyDeclMemoryCore fragExecMem instMemFrontier
  fragGasPathMem fragGasMode emitHelper emitHelperProps exprLoweringProps context compileEnv
  venomState venomInst venomExecSemantics venomExecProofs valueEncodingProps
  words arithmetic list rich_list ASCIInumbers

Theorem typed_dynarray_setup_mem_ok[local]:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok]; emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `!k w t. sa.cs_next_var <= k ==>
     eval_operand src (update_var (STRING #"%" (toString k)) w t) = eval_operand src t /\
     eval_operand dst (update_var (STRING #"%" (toString k)) w t) = eval_operand dst t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists `sa` >> simp[]) >>
  qpat_x_assum `_ sa = ((_,_,_),sb)` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND1, run_inst_seq_mem_ok_cons,
       run_inst_seq_mem_ok_last, below_frontier_MLOAD, below_frontier_MSTORE,
       below_frontier_no_ranges, step_inst_base_opcode_eqs,
       exec_read1_def, exec_write2_def, exec_pure1_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var, toString_inj] >>
  Cases_on `w2n (mload (w2n sw) s) > cap MOD dimword (:256)` >> simp[] >>
  simp[lookup_var_update_var, toString_inj] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def, not_fresh_at_def] >>
  rpt strip_tac >>
  `!k. sa.cs_next_var <= k ==> s' <> STRING #"%" (toString k)` by metis_tac[] >>
  simp[]
QED

Theorem typed_memory_dynarray_setup_path_mem[local]:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok]; emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w n /\ n <= cap /\ cap < dimword (:256) /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
      eval_operand length t = SOME (n2w n) /\
      eval_operand src_data t = SOME (sw + 32w) /\
      eval_operand dst_data t = SOME (dw + 32w) /\
      t.vs_memory = (mstore (w2n dw) (n2w n) s).vs_memory /\
      mem_word_at (w2n dw) t.vs_memory = n2w n /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_dynarray_setup_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[typed_dynarray_setup_mem_ok] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists `sa` >> simp[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl [`s`, `sa`] >> simp[]) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, mstore_mem_word_at_same] >>
  rpt conj_tac
  >- (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      simp[venom_state_component_equality])
  >- metis_tac[lookup_var_def]
  >- metis_tac[mstore_mem_bytes_at_disjoint]
  >- simp[immutableMemoryFrameTheory.immutable_mstore_capacity, MAX_DEF]
  >> gvs[venom_state_component_equality, same_blocks_def]
QED

Theorem typed_dynarray_reconstruct[local]:
  mem_word_at d u.vs_memory = n2w (LENGTH vs) /\
  (!j. j < LENGTH vs ==> val_in_memory dtv (EL j vs)
     (d + 32 + j * type_memory_size dtv) t.vs_memory) /\
  typed_copy_effect ctx func sm sb u t (d + 32)
    (LENGTH vs * type_memory_size dtv) ==>
  val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) d t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 u.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> simp[]) >>
  simp[val_in_memory_dynarray] >> conj_tac
  >- gvs[valueEncodingTheory.mem_word_at_def, valueEncodingTheory.mem_bytes_at_def] >>
  irule exprSimAggregateEncodingTheory.elems_in_memory_intro >> simp[]
QED

Theorem typed_dynarray_setup_effect[local]:
  gas_path_mem ctx func s 0 (OK u) /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!a len. a + len <= d \/ d + 32 <= a ==>
     mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
  LENGTH s.vs_memory <= LENGTH u.vs_memory /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  typed_copy_effect ctx func sa sm s u d
    (type_memory_size (ArrayTV dtv (Dynamic cap)))
Proof
  strip_tac >> simp[typed_copy_effect_def] >>
  conj_tac >- metis_tac[gas_marked_path_from_mem] >>
  conj_tac
  >- (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac
QED

Theorem typed_dynarray_finish_counted[local]:
  LENGTH vs <= cap /\
  mem_word_at d u.vs_memory = n2w (LENGTH vs) /\
  typed_copy_effect ctx func sa sm s u d
    (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
  gas_path_mem ctx func s 0 (OK u) /\
  (!x. not_fresh_at sa x ==> not_fresh_at sm x) /\
  (!j. j < LENGTH vs ==> val_in_memory dtv (EL j vs)
     (d + 32 + j * type_memory_size dtv) t.vs_memory) /\
  typed_copy_effect ctx func sm sb u t (d + 32)
    (LENGTH vs * type_memory_size dtv) /\
  gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t ==>
  val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
  typed_copy_effect ctx func sa sb s t d
    (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
  gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  strip_tac >> conj_tac >- metis_tac[typed_dynarray_reconstruct] >>
  conj_tac
  >- (irule typed_copy_effect_then >> qexistsl [`sm`, `sm`, `u`] >> simp[] >>
      irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >>
      simp[valueEncodingTheory.type_memory_size_def] >>
      `LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
      decide_tac) >>
  simp[] >> drule_all gas_path_mem_then >> simp[]
QED

(* The callback is the live-data loop, including its entry and final condition.
   It writes only the live data window, so the setup's stored header survives. *)
Theorem typed_memory_dynarray_prepare_counted:
  (do length <- emit_op MLOAD [src];
      too_long <- emit_op GT [length; Lit (n2w cap)];
      ok <- emit_op ISZERO [too_long];
      emit_void ASSERT [ok]; emit_void MSTORE [dst; length];
      src_data <- emit_op ADD [src; Lit 32w];
      dst_data <- emit_op ADD [dst; Lit 32w];
      return (length,src_data,dst_data)
   od) sa = ((length,src_data,dst_data),sm) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> not_fresh_at sm x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w (LENGTH vs) /\
  LENGTH vs <= cap /\ cap < dimword (:256) /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= w2n sw) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!u. alloca_history func u /\
    eval_operand length u = SOME (n2w (LENGTH vs)) /\
    eval_operand src_data u = SOME (sw + 32w) /\
    eval_operand dst_data u = SOME (dw + 32w) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    typed_copy_effect ctx func sa sm s u (w2n dw)
      (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
    val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) u.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?t. (!j. j < LENGTH vs ==> val_in_memory dtv (EL j vs)
          (w2n dw + 32 + j * type_memory_size dtv) t.vs_memory) /\
        typed_copy_effect ctx func sm sb u t (w2n dw + 32)
          (LENGTH vs * type_memory_size dtv) /\
        gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t) ==>
  ?t. val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  strip_tac >> drule_all typed_memory_dynarray_setup_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> rename1 `alloca_history func u` >>
  `typed_copy_effect ctx func sa sm s u (w2n dw)
     (type_memory_size (ArrayTV dtv (Dynamic cap)))` by
    (drule_all typed_dynarray_setup_effect >> simp[]) >>
  qpat_x_assum `u.vs_memory = _` kall_tac >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
     (w2n sw) u.vs_memory` by
    (irule val_in_memory_outside_write >> simp[] >>
     qexistsl [`w2n dw`, `s.vs_memory`, `type_memory_size (ArrayTV dtv (Dynamic cap))`] >>
     simp[] >> rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!u. _ ==> ?t. _` drule_all >> strip_tac >>
  qexists `t` >> irule typed_dynarray_finish_counted >>
  metis_tac[]
QED

Theorem typed_memory_dynarray_slow_forward_counted:
  compile_copy_dynarray_typed cenv dst dt cap src st sa = ((),sb) /\
  ~(type_memory_bytes cenv dt = type_memory_bytes cenv st /\ dt = st) /\
  (!sty dtyv styv value dop sop a b u dword sword.
    type_widens_to tenv sty dt /\
    evaluate_type tenv dt = SOME dtyv /\ evaluate_type tenv sty = SOME styv /\
    type_memory_bytes cenv dt = type_memory_size dtyv /\
    type_memory_bytes cenv sty = type_memory_size styv /\
    value_has_type dtyv value /\ val_wf dtyv value /\
    value_has_type styv value /\ val_wf styv value /\
    val_in_memory styv value (w2n sword) u.vs_memory /\
    (w2n sword + type_memory_size styv <= w2n dword \/
     w2n dword + type_memory_size dtyv <= w2n sword) /\
    w2n sword + type_memory_size styv < dimword (:256) /\
    w2n dword + type_memory_size dtyv < dimword (:256) /\
    compile_store_memory_typed cenv dop dt sop sty a = ((),b) /\
    (!x. dop = Var x ==> not_fresh_at a x) /\
    (!x. sop = Var x ==> not_fresh_at a x) /\
    eval_operand dop u = SOME dword /\ eval_operand sop u = SOME sword /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    alloca_history func u /\ alloca_inv u /\
    w2n sword + type_memory_size styv <= u.vs_alloca_next /\
    w2n dword + type_memory_size dtyv <= u.vs_alloca_next ==>
    ?t. val_in_memory dtyv value (w2n dword) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dword) (type_memory_size dtyv) /\
        gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t) /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= w2n sw) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) < dimword (:256) /\
  cap < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic cap)) <= s.vs_alloca_next ==>
  ?t. val_in_memory (ArrayTV dtv (Dynamic cap)) (ArrayV (DynArrayV vs))
        (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func sa sb s t (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic cap))) /\
      gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_memory_dynarray_slow_compile >> strip_tac >>
  `fn_has_code sm sb func` by
    (qpat_x_assum `fn_has_code sa sb func` mp_tac >>
     gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def, same_blocks_def]) >>
  `fn_has_code sa sm func` by suspend "setup_code" >>
  drule_all typed_copy_slow_array_control_layout >> strip_tac >>
  `(do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
       doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
       sp <- emit_op ADD [src_data; so]; dp <- emit_op ADD [dst_data; doff];
       return (sp,dp) od) stb = ((sp,dp),b4)` by
    simp[comp_bind_def, comp_return_def] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `emit_inst _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  `LENGTH vs <= cap /\ LENGTH vs <= scap` by
    metis_tac[typed_memory_dynarray_length] >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[valueEncodingPropsTheory.val_in_memory_dynarray, mem_word_at_eq_mload] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  irule typed_memory_dynarray_prepare_counted >>
  qpat_assum `_ sa = ((length,src_data,dst_data),sm)` (irule_at Any) >>
  qexists `sw` >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  suspend "loop"
QED

Resume typed_memory_dynarray_slow_forward_counted[setup_code]:
  `isPREFIX sm.cs_current_insts st1.cs_current_insts /\
   st1.cs_current_bb = sm.cs_current_bb` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`fresh_label "typed_dyn_cond" _ = _`,
        `fresh_label "typed_dyn_body" _ = _`,
        `fresh_label "typed_dyn_exit" _ = _`,
        `fresh_var _ = _`, `emit_inst ASSIGN [Lit 0w] _ _ = _`,
        `emit_inst JMP [Label hdr] _ st0 = _`] >>
     rpt (first_x_assum kall_tac) >>
     simp[fresh_label_def, fresh_var_def, emit_inst_def, fresh_id_def,
          emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  drule_all typed_copy_dynarray_slow_code_lookup >> strip_tac >>
  qpat_assum `lookup_block st1.cs_current_bb _ = _` mp_tac >>
  qpat_assum `sm.cs_current_insts <<= st1.cs_current_insts` mp_tac >>
  qpat_assum `st1.cs_current_bb = sm.cs_current_bb` mp_tac >>
  qpat_assum `same_blocks sa sm` mp_tac >>
  rpt (first_x_assum kall_tac) >>
  simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
       same_blocks_def] >> metis_tac[]
QED

Resume typed_memory_dynarray_slow_forward_counted[loop]:
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_rename_tac `alloca_history func u` >>
  `gas_path_mem ctx func u 0
    (OK (jump_to hdr ((update_var counter 0w u) with
      vs_inst_idx := u.vs_inst_idx + 1)))` by
    (irule sarray_initial_path >> simp[] >>
     qexistsl [`id1`, `id2`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func u 0 (OK initial)` >>
  `alloca_history func initial` by
    (simp[Abbr `initial`, jump_to_def, update_var_def] >>
     irule alloca_history_jump >> simp[] >> qexists `u` >> simp[]) >>
  suspend "rounds"
QED

Resume typed_memory_dynarray_slow_forward_counted[rounds]:
  `typed_copy_effect ctx func sm sth u initial (w2n dw + 32)
     (LENGTH vs * type_memory_size dtv)` by suspend "initial_effect" >>
  `?t. val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
          (w2n sw) t.vs_memory /\
       (!j. j < LENGTH vs ==> val_in_memory dtv (EL j vs)
         (w2n dw + 32 + j * type_memory_size dtv) t.vs_memory) /\
       typed_copy_effect ctx func sm sth u t (w2n dw + 32)
         (LENGTH vs * type_memory_size dtv) /\
       lookup_var counter t = SOME (n2w (LENGTH vs)) /\
       gas_path_mem ctx func initial 0 (OK t) /\ alloca_history func t` by
    (ho_match_mp_tac typed_memory_array_iteration_path_mem >>
     simp[Abbr `initial`, jump_to_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     suspend "iteration") >>
  suspend "exit"
QED

Resume typed_memory_dynarray_slow_forward_counted[initial_effect]:
  `gas_marked_path F ctx func u 0 (OK initial)` by
    metis_tac[gas_marked_path_from_mem] >>
  simp[typed_copy_effect_def, Abbr `initial`, jump_to_def, update_var_def,
       venom_state_component_equality, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume typed_memory_dynarray_slow_forward_counted[iteration]:
  conj_tac
  >- (fs[valueEncodingTheory.val_wf_def] >>
      metis_tac[exprSimPopTheory.elems_val_wf_EL]) >>
  conj_tac
  >- (gvs[valueEncodingTheory.type_memory_size_def] >>
      `LENGTH vs * type_memory_size dtv <= cap * type_memory_size dtv` by
        simp[] >> decide_tac) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "round"
QED

Resume typed_memory_dynarray_slow_forward_counted[exit]:
  drule typed_copy_effect_endpoint >> strip_tac >>
  `eval_operand length t = SOME (n2w (LENGTH vs))` by
    (qpat_assum `typed_copy_effect _ _ sm sth u t _ _` mp_tac >>
     qpat_assum `eval_operand length u = _` mp_tac >>
     qpat_assum `!x. length = Var x ==> _` mp_tac >>
     rpt (first_x_assum kall_tac) >> Cases_on `length` >>
     simp[eval_operand_def] >> rpt strip_tac >>
     imp_res_tac typed_copy_effect_record >>
     fs[venom_state_component_equality] >> metis_tac[typed_copy_effect_lookup]) >>
  `?z. typed_copy_effect ctx func sm sb t z (w2n dw + 32)
          (LENGTH vs * type_memory_size dtv) /\
        lookup_var counter z = SOME (n2w (LENGTH vs)) /\ z.vs_memory = t.vs_memory /\
        gas_path_mem ctx func t 0 (OK z) /\ alloca_history func z` by
    (irule typed_memory_array_condition_effect_counted >>
     qpat_assum `hbb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  qexists `z` >> simp[] >>
  conj_tac >- (qpat_x_assum `!j. j < LENGTH vs ==> val_in_memory dtv _ _ t.vs_memory` mp_tac >>
                rpt (first_x_assum kall_tac) >> simp[AC ADD_ASSOC ADD_COMM]) >>
  conj_tac
  >- (irule typed_copy_effect_then >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_mem_then)) >>
  qexists `t` >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_mem_then)) >>
  qexists `initial` >> simp[]
QED

Resume typed_memory_dynarray_slow_forward_counted[round]:
  drule typed_copy_effect_endpoint >> strip_tac >>
  `eval_operand length a = SOME (n2w (LENGTH vs))` by
    (qpat_assum `typed_copy_effect _ _ sm sth u a _ _` mp_tac >>
     qpat_assum `eval_operand length u = _` mp_tac >>
     qpat_assum `!x. length = Var x ==> _` mp_tac >>
     rpt (first_x_assum kall_tac) >>
     Cases_on `length` >> simp[eval_operand_def] >>
     rpt strip_tac >>
     imp_res_tac typed_copy_effect_record >>
     fs[venom_state_component_equality] >>
     metis_tac[typed_copy_effect_lookup]) >>
  irule (SRULE [lookup_var_def] typed_memory_array_round_effect_counted) >>
  qpat_assum `hbb.bb_instructions = _` (irule_at Any) >>
  simp[] >>
  qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[lookup_var_def] >>
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "element"
QED

Resume typed_memory_dynarray_slow_forward_counted[element]:
  `w2n (sw + 32w) = w2n sw + 32 /\
   w2n (dw + 32w) = w2n dw + 32` by
    (`w2n sw + 32 < dimword (:256) /\ w2n dw + 32 < dimword (:256)` by
       (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
     simp[wordsTheory.w2n_add_2]) >>
  `?v. val_in_memory dtv (EL j vs)
        (w2n (dw + 32w) + j * type_memory_size dtv) v.vs_memory /\
       typed_copy_effect ctx func stb b5 a' v
        (w2n (dw + 32w) + j * type_memory_size dtv) (type_memory_size dtv) /\
       gas_path_mem ctx func a' 0 (OK v) /\ alloca_history func v`
    suffices_by simp[AC ADD_ASSOC ADD_COMM] >>
  irule typed_memory_array_element_forward_counted >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `_ stb = ((sp,dp),b4)` (irule_at Any) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  suspend "element_premises"
QED

Resume typed_memory_dynarray_slow_forward_counted[element_premises]:
  qexists `sw + 32w` >>
  `eval_operand src_data a' = SOME (sw + 32w) /\
   eval_operand dst_data a' = SOME (dw + 32w)` by
    (qpat_assum `typed_copy_effect ctx func sm sth u a _ _` mp_tac >>
     qpat_assum `typed_copy_effect ctx func sm stb a a' _ _` mp_tac >>
     qpat_assum `eval_operand src_data u = _` mp_tac >>
     qpat_assum `eval_operand dst_data u = _` mp_tac >>
     qpat_assum `!x. src_data = Var x ==> _` mp_tac >>
     qpat_assum `!x. dst_data = Var x ==> _` mp_tac >>
     rpt (first_x_assum kall_tac) >>
     Cases_on `src_data` >> Cases_on `dst_data` >>
     simp[eval_operand_def, typed_copy_effect_def, venom_state_component_equality] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `j * type_memory_size stv + type_memory_size stv <= scap * type_memory_size stv /\
   j * type_memory_size dtv + type_memory_size dtv <= cap * type_memory_size dtv` by
    (`SUC j <= scap /\ SUC j <= cap` by decide_tac >>
     `SUC j * type_memory_size stv <= scap * type_memory_size stv /\
      SUC j * type_memory_size dtv <= cap * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC j * type_memory_size stv <= _` mp_tac >>
     qpat_x_assum `SUC j * type_memory_size dtv <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `val_in_memory stv (EL j vs) (w2n sw + 32 + j * type_memory_size stv) a.vs_memory` by
    (qpat_assum `val_in_memory (ArrayTV stv _) _ _ a.vs_memory` mp_tac >>
     pure_rewrite_tac[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
     drule exprSimAggregateEncodingTheory.elems_in_memory_EL >>
     disch_then (qspec_then `j` mp_tac) >> simp[AC ADD_ASSOC ADD_COMM]) >>
  suspend "element_finish"
QED

Resume typed_memory_dynarray_slow_forward_counted[element_finish]:
  `a'.vs_allocas = s.vs_allocas /\ a'.vs_alloca_next = s.vs_alloca_next` by
    (imp_res_tac typed_copy_effect_allocas >>
     imp_res_tac typed_copy_effect_record >>
     fs[venom_state_component_equality] >> metis_tac[]) >>
  `alloca_inv a'` by metis_tac[localPtrsPropsTheory.alloca_inv_fields] >>
  imp_res_tac typed_copy_effect_endpoint >>
  `val_wf dtv (EL j vs) /\ val_wf stv (EL j vs)` by
    (fs[valueEncodingTheory.val_wf_def] >>
     metis_tac[exprSimPopTheory.elems_val_wf_EL]) >>
  `value_has_type dtv (EL j vs) /\ value_has_type stv (EL j vs)` by
    (fs[vyperTypingTheory.value_has_type_def, vyperTypingTheory.all_have_type_EVERY] >>
     metis_tac[listTheory.EVERY_EL]) >>
  simp[lookup_var_def] >>
  fs[valueEncodingTheory.type_memory_size_def] >> decide_tac
QED

Finalise typed_memory_dynarray_slow_forward_counted
