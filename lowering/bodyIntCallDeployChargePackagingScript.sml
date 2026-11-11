(* Packaging preserves the complete ordered block stream, including multiplicity. *)
Theory bodyIntCallDeployChargePackaging
Ancestors
  vyperCompiler compileVyper loweringShapeDefs exprLoweringProps venomInst list

Theorem split_blocks_at_reconstruct:
  !blocks label prefix suffix.
    split_blocks_at label blocks = SOME (prefix,suffix) ==>
    blocks = prefix ++ suffix
Proof
  Induct_on `blocks` >- simp[split_blocks_at_def] >>
  rpt gen_tac >> rename1 `bb :: rest` >>
  simp[Once split_blocks_at_def] >>
  Cases_on `bb.bb_label = label` >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem package_internal_blocks_reconstruct:
  !descs blocks entry functions.
    package_internal_blocks descs blocks = SOME (entry,functions) ==>
    blocks = entry ++ FLAT (MAP (\func. func.fn_blocks) functions)
Proof
  Induct_on `descs` >- simp[package_internal_blocks_def] >>
  rpt gen_tac >> rename1 `desc :: rest` >> PairCases_on `desc` >>
  simp[Once package_internal_blocks_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule split_blocks_at_reconstruct >> strip_tac >>
  first_x_assum drule >>
  simp[mk_internal_function_metadata, APPEND_ASSOC]
QED

