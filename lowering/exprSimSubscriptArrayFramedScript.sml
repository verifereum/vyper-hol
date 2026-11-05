(* Length and element-layout boundaries for framed array subscripts. *)
Theory exprSimSubscriptArrayFramed
Ancestors
  exprSimSubscriptArrayFrame exprSimArrayIndex exprSimLen exprSimCopy
  exprSimAggregateEncoding exprSimProps loweringPosts vyperTypeSystem arithmetic
  emitHelperProps exprLoweringProps venomExecSemantics

(* The runtime loader of a code array's length word: a DLOAD of the data
   section at the base. *)
Theorem array_len_ok_DLOAD:
  !imm cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt (compile_ptr_load F imm LocCode) base_op ss
      (word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n b) ss.vs_data_section ++ REPLICATE 32 0w)))
Proof
  rw[array_len_ok_def, contextTheory.compile_ptr_load_def,
     contextTheory.compile_imm_load_word_runtime] >>
  imp_res_tac emit_op_extends >>
  qspecl_then [`DLOAD`, `\a s. word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))`]
    mp_tac emit_op_read1_correct >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  simp[step_inst_base_def, exec_read1_def] >> strip_tac >>
  first_x_assum (qspecl_then [`b`, `ss`] mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem immutable_array_len_ok:
  stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT et (Dynamic bound)) r w es s /\
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,es) r (Type (ArrayT et (Dynamic bound))) /\
  result_array_length cx r es = (INL n,es) /\
  eval_operand base_op s = SOME w ==>
  array_len_ok T cnt (compile_ptr_load F imm LocCode) base_op s (n2w n)
Proof
  strip_tac >> drule_all immutable_holds_data >> strip_tac >>
  `value_has_type tvt v` by gvs[immutable_holds_def] >>
  `mem_word_at (w2n w) s.vs_data_section = n2w n` by
    (irule read_result_memory_header >> simp[is_sized_type_def] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`cx`, `env`, `es`, `r`, `ArrayT et (Dynamic bound)`] >>
     simp[]) >>
  drule array_len_ok_DLOAD >>
  gvs[valueEncodingTheory.mem_word_at_def]
QED

Theorem sub_layout_array_element:
  sub_layout itv iv k (ArrayTV et bd) (ArrayV av) /\
  val_wf (ArrayTV et bd) (ArrayV av) /\
  array_index (ArrayTV et bd) av i = SOME v ==>
  sub_layout itv iv
    (k + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
     Num i * type_memory_size et) et v
Proof
  strip_tac >> Cases_on `av` >> Cases_on `bd` >>
  gvs[valueEncodingTheory.val_wf_def, vyperValueOperationTheory.array_index_def,
      AllCaseEqs(), listTheory.oEL_THM] >>
  gvs[sub_layout_def, valueEncodingTheory.type_memory_size_def]
  >~ [`ArrayV (DynArrayV vs)`]
  >- (`(Num i + 1) * type_memory_size et <= n * type_memory_size et` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      conj_tac
      >- (qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
          pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
      rpt strip_tac >> first_x_assum drule >>
      simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
      drule_all elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]) >>
  (`(Num i + 1) * type_memory_size et <= n * type_memory_size et` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!b mem. _` (qspecl_then [`b`, `mem`] mp_tac) >>
  simp[valueEncodingPropsTheory.val_in_memory_sarray] >> strip_tac >>
  metis_tac[valueEncodingProofsTheory.kvs_in_memory_lookup, ADD_ASSOC])
QED

Theorem local_path_at_step:
  local_path_at cenv cx n k tv /\ mem_step_offset tv sb = SOME (j,et) ==>
  local_path_at cenv cx n (k + j) et
Proof
  rw[local_path_at_def] >>
  qexistsl_tac [`t0`, `tv0`, `path ++ [sb]`] >> simp[] >>
  drule_all mem_path_offset_snoc >> simp[]
QED

Theorem local_val_at_array_element:
  local_val_at cenv cx n k (ArrayTV et bd) (ArrayV av) /\
  mem_step_offset (ArrayTV et bd) (ValueSubscript (IntV i)) = SOME (j,et) ==>
  local_val_at cenv cx n (k + j) et v
Proof
  simp[local_val_at_def] >> strip_tac >> disj1_tac >>
  drule_all local_path_at_step >> simp[]
QED
