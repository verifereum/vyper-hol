(* Saved-value selection after the index. Execution is the existing memory
   array boundary; ownership belongs to the snapshot, not the source place. *)
Theory exprSimCopiedSuffix
Ancestors
  exprSimCopiedValueEndpoint targetSubscriptMemory exprSimSubscriptArraySuffix
  exprSimSubscriptArraySource exprSimAttributeProps exprSimProps exprSimCopy
  exprSimDefs loweringPosts exprLoweringProps context compileEnv freshWrites
  fragGasMode fragExec gasSummary vyperState vyperMisc vyperValueOperation vyperArray
  valueEncodingTyping valueEncodingProps venomState venomMemDefs
  words integer_word integer arithmetic finite_map list

Theorem copied_array_suffix_summary:
  compile_array_subscript bop iop (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) 32 (type_memory_size etv) sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sc = (dst,sd) /\
  fn_has_code sc sd func /\ local_ptrs_reserved cenv sc /\
  local_ptrs_rel func cenv ee.scopes s /\
  sa.cs_next_var <= sc.cs_next_var /\
  stmt_state_rel ctx func cenv cx ee s /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!x. bop = Var x ==> not_fresh_at sc x) /\ (!l. bop <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  eval_operand bop s = SOME b /\ eval_operand iop s = SOME iw /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  well_formed_type_value (ArrayTV etv bd) /\
  val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n b) s.vs_memory /\
  w2n b + type_memory_size (ArrayTV etv bd) < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n b,type_memory_size (ArrayTV etv bd)) /\
  sa.cs_next_id <= aid /\ aid < sd.cs_next_id /\
  (!n lb lsz. local_region cenv ee.scopes s n lb lsz ==>
     w2n b + type_memory_size (ArrayTV etv bd) <= lb \/ lb + lsz <= w2n b) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==> FLOOKUP s.vs_allocas id = SOME entry) /\
  (!id off sz. FLOOKUP s0.vs_allocas id = SOME (off,sz) /\ id < sa.cs_next_id /\
     (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
        off + sz <= lb \/ lb + lsz <= off) ==>
     mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept cenv es ee s0 s /\ ee.gas_obs = [] /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame cenv func es sa s0 s) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?v. res = INL (Value v) /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' (Value v)
        (LocatedValue et (mk_ptr dst LocMemory)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  strip_tac >>
  `array_length (ArrayTV etv bd) av < dimword (:256)` by
    metis_tac[target_memory_array_length_bound] >>
  `(if (case bd of Fixed _ => F | Dynamic _ => T) then mload (w2n b) s
    else n2w (case bd of Fixed n => n | Dynamic _ => 0)) =
    n2w (array_length (ArrayTV etv bd) av)` by
    (Cases_on `bd` >> simp[]
     >- (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def, array_length_def]) >>
     metis_tac[target_memory_array_header]) >>
  `idx_in_range sgn iw (n2w (array_length (ArrayTV etv bd) av)) <=>
    valid_index (ArrayTV etv bd) av i` by metis_tac[array_index_word_bounds] >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "valid" >>
  suspend "invalid"
QED

Resume copied_array_suffix_summary[invalid]:
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (Cases_on `bd` >> Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  drule_all evaluate_array_subscript_oob >> strip_tac >>
  `select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i)) ee =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee)` by
    (qpat_assum `evaluate_type _ (ArrayT _ _) = _`
       (fn th => rewrite_tac[MATCH_MP select_value_result th]) >>
     simp[bind_def, lift_sum_def, raise_def]) >>
  `~idx_in_range sgn iw
    (if (case bd of Fixed _ => F | Dynamic _ => T) then mload (w2n b) s
     else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by simp[] >>
  drule_all target_memory_array_abort_path >> strip_tac >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[expr_exit_def, exit_result_def]
QED

Resume copied_array_suffix_summary[valid]:
  `?v. array_index (ArrayTV etv bd) av i = SOME v` by
    metis_tac[array_index_valid, optionTheory.IS_SOME_EXISTS] >>
  `idx_in_range sgn iw
    (if (case bd of Fixed _ => F | Dynamic _ => T) then mload (w2n b) s
     else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by simp[] >>
  drule_all target_memory_array_path >> strip_tac >>
  `select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i)) ee =
    (INL (Value v),ee)` by
    (qpat_assum `evaluate_type _ (ArrayT _ _) = _`
       (fn th => rewrite_tac[MATCH_MP select_value_result th]) >>
     simp[evaluate_subscripts_def, bind_def, lift_sum_def, return_def]) >>
  `0 <= i` by gvs[valid_index_def] >>
  `iw = n2w (Num i)` by
    (`iw = i2w i` by (Cases_on `sgn` >> gvs[i2w_pos]) >>
     `i = &Num i` by simp[integerTheory.INT_OF_NUM] >>
     qpat_x_assum `iw = i2w i` SUBST1_TAC >>
     qpat_x_assum `i = &Num i` (fn th => once_rewrite_tac[th]) >>
     rewrite_tac[i2w_pos, integerTheory.NUM_OF_INT]) >>
  qabbrev_tac `j = (case bd of Fixed _ => 0 | Dynamic _ => 32) +
    Num i * type_memory_size etv` >>
  `eval_operand dst t = SOME (b + n2w j)` by
    (qpat_assum `eval_operand dst t = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `iw = n2w _` (fn th => rewrite_tac[th]) >>
     Cases_on `bd` >> simp[NoAsms, Abbr `j`, word_mul_n2w] >>
     pure_rewrite_tac[GSYM word_add_n2w] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[WORD_ADD_ASSOC, WORD_ADD_COMM]) >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by metis_tac[value_has_type_val_wf] >>
  `mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv)` by
    metis_tac[array_element_step_offset] >>
  `j + type_memory_size etv <= type_memory_size (ArrayTV etv bd)` by
    (irule (cj 2 mem_path_offset_sound) >>
     qexists `[ValueSubscript (IntV i)]` >> simp[mem_path_offset_def]) >>
  `w2n (b + n2w j) = w2n b + j` by
    (`w2n b + j < dimword (:256)` by decide_tac >>
     `j < dimword (:256)` by decide_tac >>
     irule EQ_TRANS >> qexists `w2n b + w2n (n2w j : bytes32)` >>
     reverse conj_tac >- simp[w2n_n2w, LESS_MOD] >>
     irule w2n_add_2 >> simp[w2n_n2w, LESS_MOD]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x t = SOME w` by metis_tac[not_fresh_at_mono] >>
  `!id entry. FLOOKUP s0.vs_allocas id = SOME entry ==>
     FLOOKUP t.vs_allocas id = SOME entry` by metis_tac[] >>
  `!n lb lsz. local_region cenv ee.scopes t n lb lsz ==>
     w2n b + type_memory_size (ArrayTV etv bd) <= lb \/ lb + lsz <= w2n b` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes s n lb lsz` by
       (irule local_region_frame >> metis_tac[]) >> metis_tac[]) >>
  `locals_kept cenv es ee s0 t` by metis_tac[locals_kept_mem_tail] >>
  `~expr_has_effect (Subscript et obj idx) ==> pure_frame cenv func es sa s0 t` by
    metis_tac[pure_frame_mem_tail] >>
  `j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv` by
    simp[NoAsms, Abbr `j`] >>
  `val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n b) t.vs_memory` by metis_tac[] >>
  `FLOOKUP t.vs_allocas aid = SOME (w2n b,type_memory_size (ArrayTV etv bd))` by
    metis_tac[] >>
  `!id off sz. FLOOKUP s0.vs_allocas id = SOME (off,sz) /\ id < sa.cs_next_id /\
     (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
       off + sz <= lb \/ lb + lsz <= off) ==>
     mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory` by metis_tac[] >>
  `vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee (Value v)
     (LocatedValue et (mk_ptr dst LocMemory)) t` by
    (drule_all copied_array_value_endpoint >> simp[NoAsms]) >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  metis_tac[]
QED
Finalise copied_array_suffix_summary
