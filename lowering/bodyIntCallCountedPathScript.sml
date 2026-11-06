Theory bodyIntCallCountedPath
Ancestors
  fragGasPath gasCount fragExec venomExecSemantics venomExecProofs
  venomInstProofs venomState arithmetic list

Theorem counted_path_edge_exit:
  gas_path_edge ctx fn s n r /\ exit_result r ==>
  ?fuel bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_from fuel ctx fn s = r /\ gas_count_block fuel ctx bb s = n
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- (qexists_tac `fuel` >> simp[] >>
      conj_tac
      >- (simp_tac (srw_ss()) [run_from_def] >>
          CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
          asm_simp_tac (srw_ss()) []) >>
      simp[Once gas_count_block_def]) >>
  qexists_tac `fuel` >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def] >>
  (conj_tac
   >- (simp_tac (srw_ss()) [run_from_def] >>
       CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
       asm_simp_tac (srw_ss()) []) >>
   simp[Once gas_count_block_def])
QED
