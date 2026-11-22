(* Caller-branch closure for the production dynamic-array typed copy. *)
Theory createSizeDynarrayCopyCode
Ancestors
  createSizeSarrayCopyCode createSizeCutCode context compileEnv emitHelper venomInst pair

fun closed_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ [LET_DEF, create_cut_code_emit_inst,
                  create_cut_code_emit_op, create_cut_code_emit_void,
                  create_cut_targets_def])),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              conj_tac, gen_tac]);

Theorem create_dynarray_copy_case:
  (!d s a. create_cut_code {} a
    (SND (compile_store_memory_typed ce d dt s st a))) ==>
  !a. create_cut_code {} a
    (SND (compile_copy_dynarray_typed ce dst dt cap src st a))
Proof
  strip_tac >> gen_tac >> simp[Once compile_store_memory_typed_def] >>
  closed_steps [] >>
  IF_CASES_TAC
  >- closed_steps [compile_copy_memory_dynamic_def] >>
  ntac 4 (irule create_cut_code_bind >> (conj_tac >- simp[]) >> BETA_TAC) >>
  irule create_cut_code_ignore_bind >> (conj_tac
  >- simp[create_cut_code_emit_inst, create_cut_targets_def]) >>
  BETA_TAC >> simp[comp_ignore_bind_def] >>
  irule (SIMP_RULE (srw_ss()) [comp_bind_assoc, comp_ignore_bind_def]
    (Q.ISPECL [
      `do lt <- emit_op LT [Var ctr; len]; emit_op ISZERO [lt] od`,
      `do sofs <- emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes ce st))];
          dofs <- emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes ce dt))];
          se <- emit_op ADD [src_data; sofs];
          de <- emit_op ADD [dst_data; dofs];
          compile_store_memory_typed ce de dt se st;
          next <- emit_op ADD [Var ctr; Lit 1w];
          emit_inst ASSIGN [next] [ctr]
       od`] (Q.GEN `test` (Q.GEN `loop_body` create_sarray_loop)))) >>
  closed_steps []
QED
