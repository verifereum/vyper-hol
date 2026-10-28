Theory sourceOrdinaryProgramWitnessTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract/source_syntax",
  "../lowering/defs/bytecode/folded-value-oracle"];
val names = ["pow_folded_exp","pow_negfold_base","fold_add","fold_pow_lit","fold_cmp",
  "fold_not","fold_shift","fold_minmax","fold_powmod","fold_addmod","fold_abs",
  "keccak_literal","len_string_lit","method_id_b4","method_id_bytes","method_id_const",
  "method_id_storage","enc_mid_const","enc_mid_methodid_call","enc_mid_bytes4lit",
  "enc_ensF_string_mid","enc_ensF_uint_mid","enc_ensure_const","dec_unwrap_const",
  "ctl03_abi_method_id","enc_ensT_uint_mid","neg_lit","pow_neglit_base","lt_mixed_lit",
  "boolop_and3","i12_immut_with_storage","p29_imm_multi","c16_const_string_in_expr",
  "c27_const_binop_fold","rc09_abi_encode_data","rr03_abi"];
val () = if length names = 36 then () else raise Fail "whole program inventory";
val outcomes = map (fn name => (sourceOrdinaryProgramTestLib.witness name; true)
  handle e => (print ("BRIDGE_WITNESS_FAIL " ^ name ^ ": " ^ General.exnMessage e ^ "\n");false)) names;
val () = if List.all I outcomes then () else raise Fail "ordinary witness failures";
