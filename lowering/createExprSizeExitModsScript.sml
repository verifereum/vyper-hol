(* Relate an oversized CREATE reached within one expression invocation
   to the source initcode-size check. *)
Theory createExprSizeExitMods
Ancestors
  createExprSizeExit createExprSizeExitDefsMods
  vyperAST vyperCreate list createExprSizeExitDefs createSizeExitProxyMods createSizeExitCopyMods
  createSizeExitRawMods createSizeExitBlueprintMods

Theorem create_expr_size_exit_mods:
  !mods exps cx ty kind has_salt rof ks args d.
    EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order kind has_salt args) ==>
    create_expr_size_exit_mods mods exps cx (Call ty (CreateTarget kind has_salt rof ks) args d)
Proof
  rpt gen_tac >> Cases_on ‘kind’ >>
  simp[create_size_exit_proxy_mods, create_size_exit_copy_mods,
       create_size_exit_raw_mods, create_size_exit_blueprint_mods]
QED
