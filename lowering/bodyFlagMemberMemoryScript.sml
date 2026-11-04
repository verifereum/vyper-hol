(* FlagMember is an actual code-free constant producer. *)
Theory bodyFlagMemberMemory
Ancestors
  bodyUnopMemory bodyMemoryDefs bodyMemoryPreds exprSimLeaves exprSimHyps
  exprSimDefs exprLowering exprLoweringProps fragExecMem compileEnv valueEncoding
  vyperAST vyperInterpreter vyperState vyperTyping vyperValueOperation
  vyperTypeSystem vyperValue venomState loweringSlice

Theorem compile_flag_member_body_sim_mem:
  !ctx func cenv cx env ty ann nsid mid es.
    expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
    expr_sim_mem ctx func cenv cx ty (FlagMember ann nsid mid) es
Proof
  rpt gen_tac >> strip_tac >> rw[expr_sim_mem_def] >> PairCases_on `nsid` >>
  drule_all eval_expr_flag_member >> strip_tac >> gvs[] >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0, nsid1)) mid = i` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0, nsid1)` by gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      unwrap_value_def] >>
  irule frag_exec_mem_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def, is_word_type_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def]
QED

Theorem compile_flag_member_body_vv_sim_mem:
  !ctx func cenv cx env ty ann nsid mid es.
    expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
    expr_vv_sim_mem ctx func cenv cx ty (FlagMember ann nsid mid) es
Proof
  rpt gen_tac >> strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[compile_expr_def] >>
  conj_tac
  >- (PairCases_on `nsid` >> rpt gen_tac >>
      simp[Once evaluate_def, lookup_flag_mem_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >> rw[]) >>
  irule compile_flag_member_body_sim_mem >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_FLAG_MEMBER_MEMORY_AUDIT OK\n"
     else raise Fail "flag member memory inherited admission"
  end) [compile_flag_member_body_sim_mem, compile_flag_member_body_vv_sim_mem];
