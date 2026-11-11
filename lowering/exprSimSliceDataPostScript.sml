(* Typed posts for the ordinary slice memory tail. *)
Theory exprSimSliceDataPost
Ancestors
  loweringStateRelDefs valueEncodingDefs
  exprSimSliceData exprSimHash exprSimVVFrame
  vyperTypeSystem valueEncoding loweringPosts compileEnv context list rich_list

Theorem slice_data_bytes_success_post:
 compile_slice_data src_len src_data start len sz sa = (out,sb) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
 eval_operand src_len s = SOME (n2w (LENGTH bs)) /\
 eval_operand src_data s = SOME (n2w src_base) /\
 eval_operand start s = SOME (n2w a) /\ eval_operand len s = SOME (n2w n) /\
 (!op z. MEM op [src_len;src_data;start;len] /\ op = Var z ==> not_fresh_at sa z) /\
 mem_bytes_at src_base (LENGTH bs) s.vs_memory = bs /\
 src_base + LENGTH bs < dimword (:256) /\ a+n <= LENGTH bs /\
 32+n <= sz /\ sz < dimword (:256) /\
 expr_type e = BaseT (BytesT (Dynamic bound)) /\ n <= bound ==>
 ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
 (!k. vv_post ctx func cenv cx e es sa sb s es
   (Value (BytesV (TAKE n (DROP a bs))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory))
   (t with vs_inst_idx := k))
Proof
 strip_tac >> drule_all slice_data_success_run >> strip_tac >>
 qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
 gen_tac >> rewrite_tac[exprSimVVFrameTheory.vv_post_inst_idx] >>
 `post_value_type cenv e = expr_type e` by
   (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
 `LENGTH (TAKE n (DROP a bs)) = n` by
   (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
 `~expr_has_effect e ==> pure_frame cenv func es sa s t` by
   (strip_tac >>
    qpat_assum `wb_frame _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
    `!name b l. local_region cenv es.scopes s name b l ==>
                regions_disjoint (w2n p) sz b l` by
      (rpt strip_tac >>
       `local_region cenv es.scopes t name b l` by
         (match_mp_tac (Q.SPECL [`cenv`, `es.scopes`, `sa`, `es.scopes`, `s`, `t`]
                          exprSimPropsTheory.local_region_frame_fwd) >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
       qpat_x_assum `!name b l. local_region cenv es.scopes t _ _ _ ==> _`
         drule >> simp[]) >>
    match_mp_tac (Q.SPECL [`cenv`, `func`, `es`, `sa`, `s`, `t`, `inst`, `w2n (p:bytes32)`,
                           `sz`, `TAKE n (DROP a bs)`]
                    slice_allocated_bytes_pure_frame) >>
    qpat_assum `LENGTH (TAKE _ _) = n` (fn th => rewrite_tac[th]) >>
    qpat_assum `inst.inst_id = aid` (fn th => rewrite_tac[th]) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
 Cases_on `evaluate_type (get_tenv cx) (expr_type e)`
 >- (irule vv_post_frame_intro >>
     simp[vv_holds_def, vv_at_def, mk_ptr_def, vyperStateTheory.read_result_def] >>
     simp[vyperStateTheory.return_def]) >>
 `x = BaseTV (BytesT (Dynamic bound))` by
   (qpat_x_assum `evaluate_type _ _ = SOME x` mp_tac >>
    simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
 irule vv_post_allocated_memory_intro >>
 `LENGTH (TAKE n (DROP a bs)) = n` by
   (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
 rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
 TRY (simp[is_word_type_def, mk_ptr_def] >> NO_TAC) >>
 qexistsl_tac [`aid`, `w2n p`, `sz`,
               `BaseTV (BytesT (Dynamic bound))`, `p`] >>
 simp[mk_ptr_def, val_footprint_def] >>
 conj_tac
 >- (rpt strip_tac >> first_x_assum drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
 conj_tac
 >- (simp[val_wf_def, type_memory_size_def] >>
     mp_tac (Q.SPEC `bound` exprSimPropsTheory.le_word_size_mul) >> decide_tac) >>
 qpat_assum `LENGTH (TAKE n (DROP a bs)) = n` mp_tac >>
 POP_ASSUM_LIST (K all_tac) >>
 metis_tac[exprSimCalldataSliceTheory.bytes_buffer_write_encoding]
QED

Theorem slice_data_string_success_post:
 compile_slice_data src_len src_data start len sz sa = (out,sb) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
 eval_operand src_len s = SOME (n2w (LENGTH text)) /\
 eval_operand src_data s = SOME (n2w src_base) /\
 eval_operand start s = SOME (n2w a) /\ eval_operand len s = SOME (n2w n) /\
 (!op z. MEM op [src_len;src_data;start;len] /\ op = Var z ==> not_fresh_at sa z) /\
 mem_bytes_at src_base (LENGTH text) s.vs_memory = MAP (n2w o ORD) text /\
 src_base + LENGTH text < dimword (:256) /\ a+n <= LENGTH text /\
 32+n <= sz /\ sz < dimword (:256) /\
 expr_type e = BaseT (StringT bound) /\ n <= bound ==>
 ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
 (!k. vv_post ctx func cenv cx e es sa sb s es
   (Value (StringV (TAKE n (DROP a text))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory))
   (t with vs_inst_idx := k))
Proof
 strip_tac >>
 `mem_bytes_at src_base (LENGTH (MAP (n2w o ORD) text : word8 list)) s.vs_memory =
    MAP (n2w o ORD) text` by simp[] >>
 mp_tac (Q.INST [`bs` |-> `MAP (n2w o ORD) text : word8 list`] slice_data_success_run) >>
 (impl_tac >- simp[]) >> strip_tac >>
 qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
 gen_tac >> rewrite_tac[exprSimVVFrameTheory.vv_post_inst_idx] >>
 `post_value_type cenv e = expr_type e` by
   (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
 `LENGTH (TAKE n (DROP a (MAP (n2w o ORD) text : word8 list))) = n` by
   (simp[LENGTH_TAKE, LENGTH_DROP, LENGTH_MAP] >> decide_tac) >>
 `~expr_has_effect e ==> pure_frame cenv func es sa s t` by
   (strip_tac >>
    qpat_assum `wb_frame _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
    `!name b l. local_region cenv es.scopes s name b l ==>
                regions_disjoint (w2n p) sz b l` by
      (rpt strip_tac >>
       `local_region cenv es.scopes t name b l` by
         (match_mp_tac (Q.SPECL [`cenv`, `es.scopes`, `sa`, `es.scopes`, `s`, `t`]
                          exprSimPropsTheory.local_region_frame_fwd) >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
       qpat_x_assum `!name b l. local_region cenv es.scopes t _ _ _ ==> _`
         drule >> simp[]) >>
    match_mp_tac (Q.SPECL [`cenv`, `func`, `es`, `sa`, `s`, `t`, `inst`, `w2n (p:bytes32)`,
                           `sz`, `TAKE n (DROP a (MAP (n2w o ORD) text : word8 list))`]
                    slice_allocated_bytes_pure_frame) >>
    qpat_assum `LENGTH (TAKE _ _) = n` (fn th => rewrite_tac[th]) >>
    qpat_assum `inst.inst_id = aid` (fn th => rewrite_tac[th]) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
 Cases_on `evaluate_type (get_tenv cx) (expr_type e)`
 >- (irule vv_post_frame_intro >>
     simp[vv_holds_def, vv_at_def, mk_ptr_def, vyperStateTheory.read_result_def] >>
     simp[vyperStateTheory.return_def]) >>
 `x = BaseTV (StringT bound)` by
   (qpat_x_assum `evaluate_type _ _ = SOME x` mp_tac >>
    simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
 irule vv_post_allocated_memory_intro >>
 `LENGTH (TAKE n (DROP a text)) = n` by
   (simp[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
 rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
 TRY (simp[is_word_type_def, mk_ptr_def] >> NO_TAC) >>
 qexistsl_tac [`aid`, `w2n p`, `sz`, `BaseTV (StringT bound)`, `p`] >>
 simp[mk_ptr_def, val_footprint_def] >>
 conj_tac
 >- (rpt strip_tac >> first_x_assum drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
 conj_tac
 >- (simp[val_wf_def, type_memory_size_def] >>
     mp_tac (Q.SPEC `bound` exprSimPropsTheory.le_word_size_mul) >> decide_tac) >>
 qpat_assum `LENGTH (TAKE n (DROP a text)) = n` mp_tac >>
 POP_ASSUM_LIST (K all_tac) >>
 rewrite_tac[GSYM MAP_TAKE, GSYM MAP_DROP] >> strip_tac >>
 mp_tac (Q.SPECL [`w2n (p:bytes32)`, `MAP (n2w o ORD) (TAKE n (DROP a text)) : word8 list`,
                  `bound`, `s`] exprSimCalldataSliceTheory.bytes_buffer_write_encoding) >>
 simp[valueEncodingDefsTheory.val_in_memory_def]
QED
