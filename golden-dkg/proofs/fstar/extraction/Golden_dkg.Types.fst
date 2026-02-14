module Golden_dkg.Types
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Golden_dkg.Bundle {t_SessionId as t_SessionId}

include Golden_dkg.Bundle {SessionId as SessionId}

include Golden_dkg.Bundle {impl_5 as impl_5}

include Golden_dkg.Bundle {impl_6 as impl_6}

include Golden_dkg.Bundle {impl_7 as impl_7}

include Golden_dkg.Bundle {impl_8 as impl_8}

include Golden_dkg.Bundle {impl_9 as impl_9}

include Golden_dkg.Bundle {impl_10 as impl_10}

include Golden_dkg.Bundle {impl__random as impl_SessionId__random}

include Golden_dkg.Bundle {t_SecretScalar as t_SecretScalar}

include Golden_dkg.Bundle {SecretScalar as SecretScalar}

include Golden_dkg.Bundle {impl_1__new as impl_SecretScalar__new}

include Golden_dkg.Bundle {impl_1__inner as impl_SecretScalar__inner}

include Golden_dkg.Bundle {impl_2 as impl_2}

include Golden_dkg.Bundle {impl_3 as impl_3}

include Golden_dkg.Bundle {ark_to_bytes as ark_to_bytes}

include Golden_dkg.Bundle {ark_from_bytes as ark_from_bytes}

include Golden_dkg.Bundle {t_Ciphertext as t_Ciphertext}

include Golden_dkg.Bundle {impl_11 as impl_11}

include Golden_dkg.Bundle {impl_12 as impl_12}

include Golden_dkg.Bundle {t_MessageHeader as t_MessageHeader}

include Golden_dkg.Bundle {impl_13 as impl_13}

include Golden_dkg.Bundle {impl_14 as impl_14}

include Golden_dkg.Bundle {t_Round0Msg as t_Round0Msg}

include Golden_dkg.Bundle {impl_15 as impl_15}

include Golden_dkg.Bundle {impl_16 as impl_16}

include Golden_dkg.Bundle {t_ReshareMsg as t_ReshareMsg}

include Golden_dkg.Bundle {impl_17 as impl_17}

include Golden_dkg.Bundle {impl_18 as impl_18}

include Golden_dkg.Bundle {t_DkgOutput as t_DkgOutput}

include Golden_dkg.Bundle {impl_19 as impl_19}

include Golden_dkg.Bundle {impl_20 as impl_20}

include Golden_dkg.Bundle {t_Participant as t_Participant}

include Golden_dkg.Bundle {impl_4__new as impl_Participant__new}

include Golden_dkg.Bundle {t_DkgConfig as t_DkgConfig}

include Golden_dkg.Bundle {t_DkgDealing as t_DkgDealing}
