module

public import NPComplete.CookLevin.Main
public import NPComplete.CookLevin.Verifier.ThreeSATVerifier

@[expose] public section

namespace PvsNP

open NPComplete.CookLevin (InP PeqNP PneNP threeSAT_InP_implies_PeqNP threeSAT_inNP)
open NPComplete.SAT (ThreeSAT ValidThreeCNF)

/-- The standard Cook–Levin target in the dependency's encoded-language TM0 model. -/
theorem p_eq_np_iff_threeSat_in_p :
    PeqNP ↔ InP ValidThreeCNF.encode (ThreeSAT ∘ Subtype.val) :=
  ⟨fun h => h _ _ threeSAT_inNP, threeSAT_InP_implies_PeqNP⟩

theorem p_ne_np_iff_threeSat_not_in_p :
    PneNP ↔ ¬ InP ValidThreeCNF.encode (ThreeSAT ∘ Subtype.val) :=
  not_congr p_eq_np_iff_threeSat_in_p

end PvsNP
