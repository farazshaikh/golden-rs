module Golden_dkg.Schnorr_pok
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Golden_dkg.Bundle {t_SchnorrPoK as t_SchnorrPoK}

include Golden_dkg.Bundle {impl as impl}

include Golden_dkg.Bundle {impl_1 as impl_1}

include Golden_dkg.Bundle {prove as prove}

include Golden_dkg.Bundle {verify as verify}

include Golden_dkg.Bundle {compute_challenge as compute_challenge}
