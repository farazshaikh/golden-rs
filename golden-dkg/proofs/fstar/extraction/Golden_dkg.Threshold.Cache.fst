module Golden_dkg.Threshold.Cache
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Golden_dkg.Threshold.Bundle {t_LagrangeCache as t_LagrangeCache}

include Golden_dkg.Threshold.Bundle {impl__new as impl_LagrangeCache__new}

include Golden_dkg.Threshold.Bundle {combinations as combinations}
