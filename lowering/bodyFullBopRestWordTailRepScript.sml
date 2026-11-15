Theory bodyFullBopRestWordTailRep
Ancestors
  bodyFullBopRestWordCtorHeader bodyFullBopRestWordTailFrame
  bodyPtrBopInLiveMemory bodyPtrBopInSlotLoad bodyPtrBopInHeaderContents
  exprSimBopRestWordStorage exprSimBopRestWordLoads exprSimBopRestWordIndex
  vyperArray vyperAssignPreservesType vyperTyping vyperValueOperation exprLowering list words

(* Enumerate logical indices, rather than the stored sparse entries. *)
Theorem rest_word_membership_indexed_words[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety bd) is_in sm = (out,ct) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type et needle /\ value_has_type (ArrayTV et bd) (ArrayV av) ==>
  (evaluate_in_array (ArrayTV et bd) needle av <=>
   MEM (typed_val_to_w256 et needle)
     (GENLIST (\i. typed_val_to_w256 et
       (THE (array_index (ArrayTV et bd) av (&i))))
       (array_length (ArrayTV et bd) av)))
Proof
  strip_tac >>
  `!i. i < array_length (ArrayTV et bd) av ==>
     array_index (ArrayTV et bd) av (&i) =
       SOME (THE (array_index (ArrayTV et bd) av (&i)))` by
    (rpt strip_tac >>
     `valid_index (ArrayTV et bd) av (&i)` by simp[valid_index_def] >>
     drule array_index_valid >>
     Cases_on `array_index (ArrayTV et bd) av (&i)` >> simp[]) >>
  drule_all rest_word_array_word_membership >>
  simp[MEM_GENLIST] >> metis_tac[optionTheory.THE_DEF]
QED

(* Constructor code operands denote the robust memory supplied by the child,
   not the runtime data section. Coverage and clean contents are separate. *)
Theorem rest_word_membership_robust_index[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety cbd) is_in sm = (out,ct) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  array_index (ArrayTV et bd) av (&i) = SOME v /\
  i < array_length (ArrayTV et bd) av /\
  w2n w + type_memory_size (ArrayTV et bd) <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV et bd) (ArrayV av) (w2n w) mem) ==>
  (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) + 32 <= lo /\
  mem_word_taint tn.t_mem
    (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
  mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) s =
    typed_val_to_w256 et v
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `type_memory_size et = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `well_formed_type_value et` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type et v` by
    (irule array_index_has_type >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory et v
      (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) mem` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     drule_all rest_word_array_memory_index >> simp[]) >>
  conj_tac
  >- (drule_all rest_word_array_element_extent >> decide_tac) >>
  conj_tac
  >- (irule robust_typed_word_memory_clean >> metis_tac[]) >>
  rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  irule rest_word_memory_word >>
  metis_tac[bodyPtrDefsTheory.mem_agree_outside_def]
QED

Theorem rest_word_membership_robust_indices[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety cbd) is_in sm = (out,ct) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  w2n w + type_memory_size (ArrayTV et bd) <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV et bd) (ArrayV av) (w2n w) mem) ==>
  !i. i < array_length (ArrayTV et bd) av ==>
    (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) + 32 <= lo /\
    mem_word_taint tn.t_mem
      (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
    mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) s =
      typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&i)))
Proof
  strip_tac >> gen_tac >> disch_tac >>
  `array_index (ArrayTV et bd) av (&i) = SOME (THE (array_index (ArrayTV et bd) av (&i)))` by
    (`valid_index (ArrayTV et bd) av (&i)` by simp[valid_index_def] >>
     drule array_index_valid >> Cases_on `array_index (ArrayTV et bd) av (&i)` >> simp[]) >>
  drule_all rest_word_membership_robust_index >> simp[]
QED

Theorem rest_word_membership_robust_header[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety (Dynamic cap)) is_in sm = (out,ct) /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV et (Dynamic pcap)) (ArrayV av) (w2n w) mem) ==>
  mem_word_taint tn.t_mem (w2n w) = {} /\
  mload (w2n w) s = n2w (array_length (ArrayTV et (Dynamic cap)) av)
Proof
  strip_tac >> Cases_on `av` >> fs[value_has_type_def, array_length_def] >>
  conj_tac
  >- metis_tac[bodyPtrBopInMemoryContentsTheory.dynarray_memory_header_clean] >>
  rewrite_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  drule typedCopyLayoutPtrTheory.dynarray_in_memory_robust_length >>
  simp[bodyPtrDefsTheory.mem_agree_outside_def]
QED

Theorem rest_word_membership_ctor_rep[local]:
  compile_var_array_membership cenv needleop vv (ArrayT ety bd) is_in sm = (out,ct) /\
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  vv_holds cenv cx (ArrayT ety pbd) tv vv ee u /\
  evaluate_type (get_tenv cx) (ArrayT ety pbd) = SOME (ArrayTV et pbd) /\
  read_result cx tv ee = (INL (ArrayV av),ee) /\
  (?val. read_result cx tv ee = (INL val,ee) /\
    !rt w. evaluate_type (get_tenv cx) (ArrayT ety pbd) = SOME rt /\
      eval_operand (vv_operand vv) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
        val_in_memory rt val (w2n w) mem)) ==>
  ?w. eval_operand (vv_operand vv) u = SOME w /\
    value_has_type (ArrayTV et pbd) (ArrayV av) /\
    w2n w + type_memory_size (ArrayTV et pbd) <= lo /\
    (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV et pbd) (ArrayV av) (w2n w) mem)
Proof
  Cases_on `vv` >>
  simp[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  strip_tac >>
  fs[loweringPostsTheory.vv_holds_def] >>
  gvs[loweringPostsTheory.immutable_holds_def] >>
  metis_tac[]
QED

(* The audited Tail antecedent is kept verbatim.  All representation facts
   remain beneath its original horizon guard, including the empty family. *)
Theorem rest_word_membership_tail_clean_reads:
 !DF lo d explicit ctx fn PG cenv cx e es sa sm s0 G0 tn0 tv vv ee u Gu Tu needleop needle av ety bd pbd et is_in out ct guard.
 compile_var_array_membership cenv needleop vv (ArrayT ety bd) is_in sm = (out,ct) /\
 fn_has_code sm ct fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
 local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x. needleop = Var x \/ vv_operand vv = Var x ==> not_fresh_at sm x) /\
 is_word_type ety /\ expr_type e = ArrayT ety bd /\ post_value_type cenv e = ArrayT ety pbd /\
 (case bd of Fixed n => pbd = Fixed n | Dynamic cap => ?pcap. pbd = Dynamic pcap) /\
 (case bd of Fixed n => n | Dynamic cap => cap) < dimword (:256) /\
 ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
 (!H. guard H ==>
   read_result cx tv ee = (INL (ArrayV av),ee) /\
   evaluate_type (get_tenv cx) ety = SOME et /\
   evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME (ArrayTV et pbd) /\
   value_has_type (ArrayTV et bd) (ArrayV av) /\ value_has_type et needle /\
   eval_operand needleop u = SOME (typed_val_to_w256 et needle) /\
   op_prov (Gu H) needleop = NONE /\ op_taint (Tu H) needleop = {} /\
   vv_post H ctx fn cenv cx e es sa sm s0 ee tv vv u /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
   alloca_history fn u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
   ghost_inv_at (DF H) lo d cenv cx ee (Gu H) (Tu H) u /\
   ptr_vv_ok cx (post_value_type cenv e) tv vv ee (Gu H) (Tu H) u /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside (Tu H).t_mem u.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
   (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op (Gu H) u) /\
   (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand (Gu H) u) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 (Gu H) (Tu H)) ==>
 LENGTH (GENLIST (\i. typed_val_to_w256 et
   (THE (array_index (ArrayTV et bd) av (&i)))) (array_length (ArrayTV et bd) av)) =
   array_length (ArrayTV et bd) av /\
 (!i. i < array_length (ArrayTV et bd) av ==>
   EL i (GENLIST (\j. typed_val_to_w256 et
     (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) =
   typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&i)))) /\
 (!H. guard H ==>
   (case bd of Fixed n => LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) = n | Dynamic cap => LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) <= cap) /\
   LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) < dimword (:256) /\
   (evaluate_in_array (ArrayTV et bd) needle av <=> MEM (typed_val_to_w256 et needle) (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))) /\
   (!i. i < LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) ==>
     array_index (ArrayTV et bd) av (&i) = SOME (THE (array_index (ArrayTV et bd) av (&i))) /\
     value_has_type et (THE (array_index (ArrayTV et bd) av (&i)))) /\
   (!ib. cenv.ce_imm_alloca = SOME ib ==>
     eval_operand ib u = SOME 0w /\
     (!x. ib = Var x ==> not_fresh_at sm x) /\
     (lo <> 0 ==> op_prov (Gu H) ib = NONE /\ op_taint (Tu H) ib = {})) /\
   (!sl t Gt Tt. sm.cs_next_var <= sl.cs_next_var /\
     membership_loop_frame sl (Gu H) (Tu H) u Gt Tt t ==>
     eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
     op_prov Gt needleop = NONE /\ op_taint Tt needleop = {} /\
     eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) u /\
     op_prov Gt (vv_operand vv) = op_prov (Gu H) (vv_operand vv) /\
     op_taint Tt (vv_operand vv) = op_taint (Tu H) (vv_operand vv)) /\
   (vv_location vv = NONE \/ vv_location vv = SOME LocMemory ==>
     ?w. eval_operand (vv_operand vv) u = SOME w /\
       op_taint (Tu H) (vv_operand vv) = {} /\
       ptr_mem_ok cx (ArrayT ety pbd) (ArrayV av) (vv_operand vv) (Gu H) (Tu H) u /\
       expr_val_at cenv cx (ArrayT ety pbd) sa sm ee (ArrayV av) (vv_operand vv) u /\
       (0 < type_memory_size (ArrayTV et pbd) ==>
         w2n w + type_memory_size (ArrayTV et pbd) <= u.vs_alloca_next) /\
       (!off n src dst t G' T'. vv_operand vv = Var src /\
         0 < n /\ off + n <= type_memory_size (ArrayTV et pbd) /\
         lookup_var dst t = SOME (w + n2w off) /\
         FLOOKUP G' dst = FLOOKUP (Gu H) src /\ op_taint T' (Var dst) = {} ==>
         ptr_covers G' T' dst t n) /\
       (!i. i < LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) ==>
         mem_word_taint (Tu H).t_mem
           (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
         mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u = EL i (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))) /\
       (!cap. bd = Dynamic cap ==>
         mem_word_taint (Tu H).t_mem (w2n w) = {} /\
         mload (w2n w) u = n2w (LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))))) /\
   (!tr. vv_location vv = SOME (if tr then LocTransient else LocStorage) ==>
     ?w. eval_operand (vv_operand vv) u = SOME w /\
       op_taint (Tu H) (vv_operand vv) = {} /\
       storage_holds cx tr (ArrayT ety pbd) tv w ee u /\
       (!i. i < LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) ==>
         key_taint (if tr then (Tu H).t_trans else (Tu H).t_stor)
           (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) = {} /\
         (if tr then tload (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) u
          else sload (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) u) = EL i (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))) /\
       (!cap. bd = Dynamic cap ==>
         key_taint (if tr then (Tu H).t_trans else (Tu H).t_stor) w = {} /\
         (if tr then tload w u else sload w u) = n2w (LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))))) /\
   (~cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?w. eval_operand (vv_operand vv) u = SOME w /\
       op_taint (Tu H) (vv_operand vv) = {} /\
       immutable_holds cenv cx (ArrayT ety pbd) (Value (ArrayV av)) w ee u /\
       value_has_type (ArrayTV et pbd) (ArrayV av) /\
       w2n w + type_memory_size (ArrayTV et pbd) <= LENGTH u.vs_data_section /\
       (!i. i < LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) ==>
         word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n (w + n2w
             ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)))
             u.vs_data_section ++ REPLICATE 32 0w)) = EL i (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))) /\
       (!cap. bd = Dynamic cap ==>
         word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n w) u.vs_data_section ++ REPLICATE 32 0w)) =
           n2w (LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))))) /\
   (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?w. eval_operand (vv_operand vv) u = SOME w /\
       op_prov (Gu H) (vv_operand vv) = NONE /\ op_taint (Tu H) (vv_operand vv) = {} /\
       w2n w + type_memory_size (ArrayTV et pbd) <= lo /\
       (!i. i < LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av)) ==>
         (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) + 32 <= lo /\
         mem_word_taint (Tu H).t_mem
           (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
         mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u = EL i (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))) /\
       (!cap. bd = Dynamic cap ==>
         w2n w + 32 <= lo /\ mem_word_taint (Tu H).t_mem (w2n w) = {} /\
         mload (w2n w) u = n2w (LENGTH (GENLIST (\j. typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&j)))) (array_length (ArrayTV et bd) av))))))
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [LET_THM] >> BETA_TAC >>
  conj_tac >- simp[] >> conj_tac >- simp[EL_GENLIST] >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!H. guard H ==> _` (qspec_then `H` mp_tac) >>
  simp[] >> strip_tac >>
  `!i. i < array_length (ArrayTV et bd) av ==>
    array_index (ArrayTV et bd) av (&i) = SOME (THE (array_index (ArrayTV et bd) av (&i))) /\
    value_has_type et (THE (array_index (ArrayTV et bd) av (&i)))` by
    (rpt strip_tac >>
     `valid_index (ArrayTV et bd) av (&i)` by simp[valid_index_def] >>
     drule array_index_valid >>
     Cases_on `array_index (ArrayTV et bd) av (&i)` >> simp[] >>
     irule array_index_has_type >> metis_tac[evaluate_type_well_formed]) >>
  `case bd of Fixed n => array_length (ArrayTV et bd) av = n
    | Dynamic cap => array_length (ArrayTV et bd) av <= cap` by
    (Cases_on `bd` >> Cases_on `av` >> gvs[value_has_type_def, array_length_def]) >>
  conj_tac >- simp[] >>
  conj_tac >- (Cases_on `bd` >> gvs[] >> decide_tac) >>
  conj_tac >- (irule rest_word_membership_indexed_words >> metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "immutable_base" >>
  conj_tac
  >- (rpt strip_tac >>
      `!x. needleop = Var x ==> not_fresh_at sl x` by
        metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      `!x. vv_operand vv = Var x ==> not_fresh_at sl x` by
        metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[bodyPtrBopInLoopContractTheory.membership_loop_frame_operand]) >>
  conj_tac >- suspend "runtime_memory" >>
  conj_tac >- suspend "runtime_slot" >>
  conj_tac >- suspend "runtime_code" >> suspend "ctor"
QED

Resume rest_word_membership_tail_clean_reads[ctor]:
  strip_tac >>
  `vv_holds cenv cx (ArrayT ety pbd) tv vv ee u` by
    (fs[loweringPostsTheory.vv_post_def] >> metis_tac[]) >>
  `?w. eval_operand (vv_operand vv) u = SOME w /\
    value_has_type (ArrayTV et pbd) (ArrayV av) /\
    w2n w + type_memory_size (ArrayTV et pbd) <= lo /\
    (!mem. mem_agree_outside (Tu H).t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV et pbd) (ArrayV av) (w2n w) mem)` by
    (irule rest_word_membership_ctor_rep >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `w` >> simp[] >> suspend "ctor_reads"
QED

Resume rest_word_membership_tail_clean_reads[ctor_reads]:
  `op_prov (Gu H) (vv_operand vv) = NONE /\ op_taint (Tu H) (vv_operand vv) = {}` by
    (Cases_on `vv` >> gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def,
      bodyPtrDefsTheory.ptr_vv_ok_def]) >>
  simp[] >> conj_tac
  >- suspend "ctor_elements" >>
  suspend "ctor_length"
QED


Resume rest_word_membership_tail_clean_reads[ctor_elements]:
  `!i. i < array_length (ArrayTV et pbd) av ==>
    w2n w + (case pbd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <= lo /\
    mem_word_taint (Tu H).t_mem
      (w2n w + (case pbd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
    mload (w2n w + (case pbd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u =
      typed_val_to_w256 et (THE (array_index (ArrayTV et pbd) av (&i)))` by
    metis_tac[rest_word_membership_robust_indices] >>
  Cases_on `bd` >> gvs[] >>
  Cases_on `av` >> gvs[value_has_type_def, array_length_def, array_index_def]
QED

Resume rest_word_membership_tail_clean_reads[ctor_length]:
  gen_tac >> disch_tac >> gvs[] >>
  `mem_word_taint (Tu H).t_mem (w2n w) = {} /\
    mload (w2n w) u = n2w (array_length (ArrayTV et (Dynamic cap)) av)` by
    metis_tac[rest_word_membership_robust_header] >>
  simp[] >>
  Cases_on `av` >>
  gvs[value_has_type_def, valueEncodingTheory.type_memory_size_def] >> decide_tac
QED

Resume rest_word_membership_tail_clean_reads[runtime_memory]:
  strip_tac >>
  `vv_holds cenv cx (ArrayT ety pbd) tv vv ee u` by
    (fs[loweringPostsTheory.vv_post_def] >> metis_tac[]) >>
  `?w. eval_operand (vv_operand vv) u = SOME w /\
    op_taint (Tu H) (vv_operand vv) = {} /\
    ptr_mem_ok cx (ArrayT ety pbd) (ArrayV av) (vv_operand vv) (Gu H) (Tu H) u` by
    (Cases_on `vv` >>
     gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def,
       loweringPostsTheory.vv_holds_def, loweringPostsTheory.expr_val_rel_def,
       bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_val_ok_def,
       compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `expr_val_at cenv cx (ArrayT ety pbd) sa sm ee (ArrayV av) (vv_operand vv) u` by
    (`vv_at cenv cx (ArrayT ety pbd) sa sm ee tv vv u` by
       (fs[loweringPostsTheory.vv_post_def] >> gvs[]) >>
     Cases_on `vv`
     >- gvs[loweringPostsTheory.vv_at_def, contextTheory.vv_operand_def] >>
     gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
     drule_all bodyPtrBopInRepresentationTheory.membership_memory_value_at >> simp[]) >>
  `stmt_state_rel H ctx fn cenv cx ee u` by fs[loweringPostsTheory.vv_post_def] >>
  `~is_word_type (ArrayT ety pbd)` by simp[compileEnvTheory.is_word_type_def] >>
  `val_footprint (ArrayTV et pbd) (ArrayV av) = type_memory_size (ArrayTV et pbd)` by
    simp[loweringPostsTheory.val_footprint_def] >>
  `(0 < type_memory_size (ArrayTV et pbd) ==>
     w2n w + type_memory_size (ArrayTV et pbd) <= u.vs_alloca_next)` by
    (drule_all externalReturnBoundsTheory.expr_val_at_frontier >> simp[] >> metis_tac[]) >>
  `!off n src dst t G' T'. vv_operand vv = Var src /\
    0 < n /\ off + n <= type_memory_size (ArrayTV et pbd) /\
    lookup_var dst t = SOME (w + n2w off) /\
    FLOOKUP G' dst = FLOOKUP (Gu H) src /\ op_taint T' (Var dst) = {} ==>
    ptr_covers G' T' dst t n` by
    (rpt strip_tac >>
      `expr_val_at cenv cx (ArrayT ety pbd) sa sm ee (ArrayV av) (Var src) u` by metis_tac[] >>
      `ptr_val_ok cx (ArrayT ety pbd) (ArrayV av) (Var src) (Gu H) (Tu H) u` by
        gvs[bodyPtrDefsTheory.ptr_val_ok_def] >>
      `lookup_var src u = SOME w` by gvs[venomStateTheory.eval_operand_def] >>
      `off + n <= val_footprint (ArrayTV et pbd) (ArrayV av)` by simp[] >>
      drule_all typedCopyPtrTheory.expr_val_at_ptr_offset_read_covers >> simp[]) >>
  qexists_tac `w` >> fs[] >> suspend "memory_reads"
QED

Resume rest_word_membership_tail_clean_reads[memory_reads]:
  markerLib.RESUME_TAC >> (gvs[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!mem. mem_agree_outside (Tu H).t_mem u.vs_memory mem ==>
    val_in_memory (ArrayTV et pbd) (ArrayV av) (w2n w) mem` by
    (fs[bodyPtrDefsTheory.ptr_mem_ok_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside (Tu H).t_mem u.vs_memory mem ==>
    val_in_memory (ArrayTV et bd) (ArrayV av) (w2n w) mem` by
    (Cases_on `bd` >> Cases_on `av` >>
     gvs[value_has_type_def, valueEncodingDefsTheory.val_in_memory_def]) >>
  conj_tac
  >- (`!i. i < array_length (ArrayTV et bd) av ==>
        w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <=
          w2n w + type_memory_size (ArrayTV et bd) /\
        mem_word_taint (Tu H).t_mem
          (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
        mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u =
          typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&i)))` by
        metis_tac[rest_word_membership_robust_indices, arithmeticTheory.LESS_EQ_REFL] >>
      gvs[]) >>
  gen_tac >> disch_tac >> gvs[] >>
  metis_tac[rest_word_membership_robust_header])
QED

Resume rest_word_membership_tail_clean_reads[runtime_slot]:
  gen_tac >> strip_tac >>
  `vv_holds cenv cx (ArrayT ety pbd) tv vv ee u` by
    (fs[loweringPostsTheory.vv_post_def] >> metis_tac[]) >>
  Cases_on `vv` >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  rename1 `LocatedValue ann p` >>
  `?w. eval_operand p.ptr_operand u = SOME w /\
    storage_holds cx tr (ArrayT ety pbd) tv w ee u` by
    (Cases_on `tr` >>
     gvs[loweringPostsTheory.vv_holds_def] >> metis_tac[]) >>
  qexists_tac `w` >>
  `op_taint (Tu H) p.ptr_operand = {}` by
    gvs[bodyPtrDefsTheory.ptr_vv_ok_def] >>
  simp[] >> suspend "slot_reads"
QED

Resume rest_word_membership_tail_clean_reads[slot_reads]:
  conj_tac
  >- (gen_tac >> disch_tac >>
      `i < array_length (ArrayTV et pbd) av /\
       array_index (ArrayTV et pbd) av (&i) =
         SOME (THE (array_index (ArrayTV et bd) av (&i))) /\
       (case pbd of Fixed _ => 0 | Dynamic _ => 1) =
         (case bd of Fixed _ => 0 | Dynamic _ => 1)` by
        (Cases_on `bd` >> Cases_on `av` >>
         gvs[value_has_type_def, array_length_def, array_index_def]) >>
      `key_taint (if tr then (Tu H).t_trans else (Tu H).t_stor)
         (w + n2w ((case pbd of Fixed _ => 0 | Dynamic _ => 1) + i)) = {}` by
        (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)
           membership_storage_array_key_clean >>
         disch_then drule >> simp[] >> metis_tac[]) >>
      ` (if tr then tload (w + n2w ((case pbd of Fixed _ => 0 | Dynamic _ => 1) + i)) u
          else sload (w + n2w ((case pbd of Fixed _ => 0 | Dynamic _ => 1) + i)) u) =
          typed_val_to_w256 et (THE (array_index (ArrayTV et bd) av (&i)))` by
        (irule rest_word_storage_array_load >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      gvs[value_has_type_def, array_length_def, array_index_def, rest_word_storage_array_load]) >>
  gen_tac >> disch_tac >> gvs[] >>
  `key_taint (if tr then (Tu H).t_trans else (Tu H).t_stor) w = {} /\
   (if tr then tload w u else sload w u) =
     n2w (array_length (ArrayTV et (Dynamic pcap)) av)` by
    (drule_all membership_located_slot_header >> simp[]) >>
  Cases_on `av` >> gvs[value_has_type_def, array_length_def]
QED

Resume rest_word_membership_tail_clean_reads[runtime_code]:
  strip_tac >>
  `vv_holds cenv cx (ArrayT ety pbd) tv vv ee u` by
    (fs[loweringPostsTheory.vv_post_def] >> metis_tac[]) >>
  Cases_on `vv` >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  rename1 `LocatedValue ann p` >>
  `?w. eval_operand p.ptr_operand u = SOME w /\
    immutable_holds cenv cx (ArrayT ety pbd) tv w ee u` by
    (gvs[loweringPostsTheory.vv_holds_def] >> metis_tac[]) >>
  `immutable_holds cenv cx (ArrayT ety pbd) (Value (ArrayV av)) w ee u` by
    (gvs[loweringPostsTheory.immutable_holds_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def] >> metis_tac[]) >>
  `value_has_type (ArrayTV et pbd) (ArrayV av)` by
    (gvs[loweringPostsTheory.immutable_holds_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx fn cenv cx ee u` by
    fs[loweringPostsTheory.vv_post_def] >>
  `op_taint (Tu H) p.ptr_operand = {}` by
    gvs[bodyPtrDefsTheory.ptr_vv_ok_def] >>
  `w2n w + type_memory_size (ArrayTV et pbd) <= LENGTH u.vs_data_section` by
    (drule_all exprSimBopRestWordLoadSafetyTheory.rest_word_immutable_region_bound >> simp[]) >>
  qexists_tac `w` >> simp[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `i < array_length (ArrayTV et pbd) av /\
       array_index (ArrayTV et pbd) av (&i) =
         SOME (THE (array_index (ArrayTV et bd) av (&i))) /\
       (case pbd of Fixed _ => 0 | Dynamic _ => 32) =
         (case bd of Fixed _ => 0 | Dynamic _ => 32)` by
        (Cases_on `bd` >> Cases_on `av` >>
         gvs[value_has_type_def, array_length_def, array_index_def]) >>
      drule_all bodyPtrBopInCodeContentsTheory.membership_array_immutable_dload >> simp[]) >>
  gen_tac >> disch_tac >> gvs[] >>
  drule_all membership_dynamic_code_header >>
  Cases_on `av` >> simp[array_length_def]
QED

Resume rest_word_membership_tail_clean_reads[immutable_base]:
  gen_tac >> disch_tac >>
  `stmt_state_rel H ctx fn cenv cx ee u` by fs[loweringPostsTheory.vv_post_def] >>
  conj_tac
  >- (drule_all bodyPtrBopInRepresentationTheory.membership_immutable_base_value >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base,
        freshWritesTheory.not_fresh_at_mono]) >>
  Cases_on `ib` >>
  gvs[bodyPtrDefsTheory.ghost_inv_at_def, ptrDisciplineTheory.op_prov_def,
    ptrDisciplineTheory.op_taint_def]
QED

Finalise rest_word_membership_tail_clean_reads
