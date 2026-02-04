From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import Why3.Qed.Qed.
Require Import Why3.Memory.Memory.
Open Scope Z_scope.
Axiom Q_K_known_dn_oids_8603_region : region (- 8604%Z) = 0%Z.
Axiom Q_K_known_dn_oids_8603_linked : forall  (t : Z -> Z) (fact0 : linked t), t (- 8604%Z) = 48%Z.
Axiom Q_K_known_ext_oids_8681_region : region (- 8682%Z) = 0%Z.
Axiom Q_K_known_ext_oids_8681_linked : forall  (t : Z -> Z) (fact0 : linked t), t (- 8682%Z) = 87%Z.
Axiom Q_K_known_kp_oids_8644_region : region (- 8645%Z) = 0%Z.
Axiom Q_K_known_kp_oids_8644_linked : forall  (t : Z -> Z) (fact0 : linked t), t (- 8645%Z) = 14%Z.
Axiom Q_G_parse_rdn_val_cn_8589_region : region 8590%Z = 0%Z.
Axiom Q_G_parse_rdn_val_cn_8589_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8590%Z = 1%Z.
Axiom Q_G_parse_rdn_val_x520name_8590_region : region 8591%Z = 0%Z.
Axiom Q_G_parse_rdn_val_x520name_8590_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8591%Z = 1%Z.
Axiom Q_G_parse_rdn_val_serial_8591_region : region 8592%Z = 0%Z.
Axiom Q_G_parse_rdn_val_serial_8591_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8592%Z = 1%Z.
Axiom Q_G_parse_rdn_val_country_8592_region : region 8593%Z = 0%Z.
Axiom Q_G_parse_rdn_val_country_8592_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8593%Z = 1%Z.
Axiom Q_G_parse_rdn_val_locality_8593_region : region 8594%Z = 0%Z.
Axiom Q_G_parse_rdn_val_locality_8593_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8594%Z = 1%Z.
Axiom Q_G_parse_rdn_val_state_8594_region : region 8595%Z = 0%Z.
Axiom Q_G_parse_rdn_val_state_8594_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8595%Z = 1%Z.
Axiom Q_G_parse_rdn_val_org_8595_region : region 8596%Z = 0%Z.
Axiom Q_G_parse_rdn_val_org_8595_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8596%Z = 1%Z.
Axiom Q_G_parse_rdn_val_org_unit_8596_region : region 8597%Z = 0%Z.
Axiom Q_G_parse_rdn_val_org_unit_8596_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8597%Z = 1%Z.
Axiom Q_G_parse_rdn_val_title_8597_region : region 8598%Z = 0%Z.
Axiom Q_G_parse_rdn_val_title_8597_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8598%Z = 1%Z.
Axiom Q_G_parse_rdn_val_dn_qual_8598_region : region 8599%Z = 0%Z.
Axiom Q_G_parse_rdn_val_dn_qual_8598_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8599%Z = 1%Z.
Axiom Q_G_parse_rdn_val_pseudo_8602_region : region 8603%Z = 0%Z.
Axiom Q_G_parse_rdn_val_pseudo_8602_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8603%Z = 1%Z.
Axiom Q_G_parse_rdn_val_dc_8601_region : region 8602%Z = 0%Z.
Axiom Q_G_parse_rdn_val_dc_8601_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8602%Z = 1%Z.
Axiom Q_K_null_encoded_val_8560_region : region (- 8561%Z) = 0%Z.
Axiom Q_K_null_encoded_val_8560_linked : forall  (t : Z -> Z) (fact0 : linked t), t (- 8561%Z) = 2%Z.
Axiom Q_K__id_kp_anyEKU_8637_region : region (- 8638%Z) = 0%Z.
Axiom Q_K__id_kp_anyEKU_8637_linked : forall  (t : Z -> Z) (fact0 : linked t), t (- 8638%Z) = 10%Z.
Axiom Q_G_parse_algoid_params_generic_8423_region : region 8424%Z = 0%Z.
Axiom Q_G_parse_algoid_params_generic_8423_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8424%Z = 1%Z.
Axiom Q_G_parse_algoid_params_ecdsa_with_8418_region : region 8419%Z = 0%Z.
Axiom Q_G_parse_algoid_params_ecdsa_with_8418_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8419%Z = 1%Z.
Axiom Q_G_parse_algoid_params_ecPublicKey_8419_region : region 8420%Z = 0%Z.
Axiom Q_G_parse_algoid_params_ecPublicKey_8419_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8420%Z = 1%Z.
Axiom Q_G_parse_algoid_params_rsa_8424_region : region 8425%Z = 0%Z.
Axiom Q_G_parse_algoid_params_rsa_8424_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8425%Z = 1%Z.
Axiom Q_G_parse_ext_AIA_8617_region : region 8618%Z = 0%Z.
Axiom Q_G_parse_ext_AIA_8617_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8618%Z = 1%Z.
Axiom Q_G_parse_ext_AKI_8618_region : region 8619%Z = 0%Z.
Axiom Q_G_parse_ext_AKI_8618_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8619%Z = 1%Z.
Axiom Q_G_parse_ext_SKI_8619_region : region 8620%Z = 0%Z.
Axiom Q_G_parse_ext_SKI_8619_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8620%Z = 1%Z.
Axiom Q_G_parse_ext_keyUsage_8621_region : region 8622%Z = 0%Z.
Axiom Q_G_parse_ext_keyUsage_8621_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8622%Z = 1%Z.
Axiom Q_G_parse_ext_certPolicies_8628_region : region 8629%Z = 0%Z.
Axiom Q_G_parse_ext_certPolicies_8628_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8629%Z = 1%Z.
Axiom Q_G_parse_ext_policyMapping_8629_region : region 8630%Z = 0%Z.
Axiom Q_G_parse_ext_policyMapping_8629_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8630%Z = 1%Z.
Axiom Q_G_parse_ext_SAN_8630_region : region 8631%Z = 0%Z.
Axiom Q_G_parse_ext_SAN_8630_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8631%Z = 1%Z.
Axiom Q_G_parse_ext_IAN_8631_region : region 8632%Z = 0%Z.
Axiom Q_G_parse_ext_IAN_8631_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8632%Z = 1%Z.
Axiom Q_G_parse_ext_subjectDirAttr_8632_region : region 8633%Z = 0%Z.
Axiom Q_G_parse_ext_subjectDirAttr_8632_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8633%Z = 1%Z.
Axiom Q_G_parse_ext_basicConstraints_8633_region : region 8634%Z = 0%Z.
Axiom Q_G_parse_ext_basicConstraints_8633_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8634%Z = 1%Z.
Axiom Q_G_parse_ext_nameConstraints_8635_region : region 8636%Z = 0%Z.
Axiom Q_G_parse_ext_nameConstraints_8635_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8636%Z = 1%Z.
Axiom Q_G_parse_ext_policyConstraints_8636_region : region 8637%Z = 0%Z.
Axiom Q_G_parse_ext_policyConstraints_8636_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8637%Z = 1%Z.
Axiom Q_G_parse_ext_EKU_8646_region : region 8647%Z = 0%Z.
Axiom Q_G_parse_ext_EKU_8646_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8647%Z = 1%Z.
Axiom Q_G_parse_ext_CRLDP_8649_region : region 8650%Z = 0%Z.
Axiom Q_G_parse_ext_CRLDP_8649_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8650%Z = 1%Z.
Axiom Q_G_parse_ext_inhibitAnyPolicy_8650_region : region 8651%Z = 0%Z.
Axiom Q_G_parse_ext_inhibitAnyPolicy_8650_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8651%Z = 1%Z.
Axiom Q_G_parse_ext_bad_oid_8667_region : region 8668%Z = 0%Z.
Axiom Q_G_parse_ext_bad_oid_8667_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8668%Z = 1%Z.
Axiom Q_G_parse_sig_ecdsa_8417_region : region 8418%Z = 0%Z.
Axiom Q_G_parse_sig_ecdsa_8417_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8418%Z = 1%Z.
Axiom Q_G_parse_sig_generic_8422_region : region 8423%Z = 0%Z.
Axiom Q_G_parse_sig_generic_8422_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8423%Z = 1%Z.
Axiom Q_L_param_7105_region : region 7106%Z = 2%Z.
Axiom Q_L_param_7105_linked : forall  (t : Z -> Z) (fact0 : linked t), t 7106%Z = 0%Z.
Axiom Q_G_parse_subjectpubkey_ec_8420_region : region 8421%Z = 0%Z.
Axiom Q_G_parse_subjectpubkey_ec_8420_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8421%Z = 1%Z.
Axiom Q_G_parse_subjectpubkey_rsa_8421_region : region 8422%Z = 0%Z.
Axiom Q_G_parse_subjectpubkey_rsa_8421_linked : forall  (t : Z -> Z) (fact0 : linked t), t 8422%Z = 1%Z.
