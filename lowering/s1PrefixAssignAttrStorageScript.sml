(* Request-prefix companion to bodyFullAssignAttrStorage. *)
Theory s1PrefixAssignAttrStorage
Ancestors
  s1PrefixPreds bodyFullAssignAttrStorage s1PrefixDefs

Theorem compile_assign_attr_storage_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty env
   src id fld sid fty fsz e es ts tr id_str slot.
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      SOME (fty,fsz) /\
  is_word_type fty /\
  expr_type e = fty /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
  expr_body_pre cenv cx env e es ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty
        (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ty
        (gas_shadow_stmt
          (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)))
      (eval_stmt cx
        (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)) es
Proof
  cheat
QED
