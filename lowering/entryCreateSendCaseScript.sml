(* Keep the Send-case geometry exports at their original qualified names. *)
Theory entryCreateSendCase
Ancestors
  entryCreateSendSuffix

Theorem create_send_effect_code = entryCreateSendSuffixTheory.create_send_effect_code;

Theorem create_send_effect_cut = entryCreateSendSuffixTheory.create_send_effect_cut;

Theorem create_send_effect_layout = entryCreateSendSuffixTheory.create_send_effect_layout;

Theorem create_send_effect_ok_scope = entryCreateSendSuffixTheory.create_send_effect_ok_scope;

Theorem create_send_effect_abort_scope = entryCreateSendSuffixTheory.create_send_effect_abort_scope;
