Theory bodyPtrPrecompileBuiltinsOperandTransport
Ancestors bodyPtrPrecompileBuiltinsArithmeticValue valueTypingMemoryProps
          valueEncodingProps exprSimProps bodyPtrDefs loweringPosts

Theorem ec_point_ptr_reconstruct:
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) /\
  ~is_word_type ty /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  expr_val_rel cx ty v (Var dst) s /\
  eval_operand (Var dst) s = SOME w /\
  ptr_covers G tn dst s 64 /\
  (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn.t_mem) ==>
  ptr_val_ok cx ty v (Var dst) G tn s
Proof
  strip_tac >>
  `val_wf (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v` by
    metis_tac[value_has_type_memory_wf] >>
  `val_store_size (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v <= 64` by
    (drule val_store_size_le >> simp[valueEncodingTheory.type_memory_size_def]) >>
  simp[ptr_val_ok_def] >> conj_tac
  >- gvs[ptr_covers_def] >>
  simp[ptr_mem_ok_def] >> conj_tac
  >- (rpt strip_tac >> irule val_in_memory_mem_agree >>
      conj_tac >- simp[] >>
      qexistsl [`64`, `s.vs_memory`] >>
      simp[valueEncodingTheory.type_memory_size_def] >> conj_tac
      >- (irule clean_window_mem_agree >> qexists `tn.t_mem` >> simp[]) >>
      gvs[expr_val_rel_def]) >>
  gvs[ptr_covers_def, venomStateTheory.eval_operand_def] >>
  qexistsl [`b`, `sz'`] >> simp[]
QED
