(* Continuing paths keep the runtime data section available to later loads. *)
Theory gasPathDataSection
Ancestors fragGasPath intCallReturn venomState venomInst venomInstProofs fragExec
val _ = Parse.hide "finish";

Theorem gas_path_data_section:
  gas_path ctx fn start n (OK finish) ==>
  finish.vs_data_section = start.vs_data_section
Proof
  `!ctx fn s n t. gas_path_edge ctx fn s n (OK t) ==>
      t.vs_data_section = s.vs_data_section` by
    (rpt gen_tac >> rw[gas_path_edge_def] >> gvs[exit_result_def] >>
     imp_res_tac (cj 1 (REWRITE_RULE [DISJ_IMP_THM] (SPEC_ALL step_inst_data_section))) >>
     imp_res_tac eval_phis_data_section >> gvs[jump_to_def] >>
     qpat_assum `OK t = step_inst _ _ _ _` (fn result =>
       qpat_assum `exit_result (step_inst _ _ _ _)`
         (mp_tac o PURE_REWRITE_RULE [GSYM result])) >>
     simp[NoAsms, exit_result_def]) >>
  `!ctx fn start n r. gas_path ctx fn start n r ==>
      !finish. r = OK finish ==> finish.vs_data_section = start.vs_data_section`
    suffices_by (disch_then (qspecl_then [`ctx`,`fn`,`start`,`n`,`OK finish`] mp_tac) >>
                 simp[NoAsms]) >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac >> rpt strip_tac >>
  gvs[exit_result_def] >> drule_then (fn frame => simp[NoAsms, frame])
    (ASSUME ``!ctx fn s n t. gas_path_edge ctx fn s n (OK t) ==>
      t.vs_data_section = s.vs_data_section``)
QED
