Theory sourceTypeFrontendLibTest
Ancestors
  sourceTypeTest sourceTypeDefs sourceTypeResolve sourceTypeProps
  sourceConstAST sourceConstAnnotation vyperAST finite_map
Libs
  sourceTypeFrontendLib

val input : sourceTypeFrontendLib.input =
  {type_env=``FEMPTY : (nsid,type_args) fmap``,
   names=``source_type_test_names``, constants=``[] : (string list # source_const_binding) list``,
   annotation=``SCA_Bytes (SCE_Binary SCB_Add
      (SCE_Literal (SCL_Int 2)) (SCE_Literal (SCL_Int 3)))``};
val cert = sourceTypeFrontendLib.resolve input;
val _ = save_thm ("source_type_frontend_equation", #equation cert);
val _ = save_thm ("source_type_frontend_well_formed", #well_formed cert);
val _ = save_thm ("source_type_frontend_provenance", #provenance cert);
val _ = save_thm ("source_type_frontend_original_bounds", #original_bounds cert);
val claimed = sourceTypeFrontendLib.check_claim input
  ``Type (BaseT (BytesT (Dynamic 5)))``;
val _ = save_thm ("source_type_frontend_claim", valOf (#claim claimed));

val rejected =
  (sourceTypeFrontendLib.check_claim input ``Type (BaseT (BytesT (Dynamic 6)))``;
   false) handle HOL_ERR _ => true;
val _ = if rejected then () else raise Fail "false inferred bound accepted";

val shadowed : sourceTypeFrontendLib.input =
  {type_env= #type_env input, constants= #constants input,
   annotation= #annotation input, names=``[(["Bytes"],STI_Bool)]``};
val rejected = (sourceTypeFrontendLib.resolve shadowed; false)
  handle HOL_ERR _ => true;
val _ = if rejected then () else raise Fail "shadowed constructor accepted";
